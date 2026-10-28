#!/usr/bin/env python3
"""TCG Price Checker - compares every sealed product in a Shopify shop with TCGplayer prices.

Easiest: use the app ("TCG Price Checker.exe" on Windows, "TCG Price Checker.app" on Mac). It needs nothing
installed and can be moved anywhere; its saved choices, cache and reports live in the folder next to it.

Making the app (once per computer type, needs Python 3.10+ from python.org):
  * Mac:      open Terminal and run   python3 tcg_price_checker.py --build-app
              (Macs have no "python" command, only "python3", after installing Python from python.org)
  * Windows:  py tcg_price_checker.py --build-app
The app appears next to this file. Copying a Mac app to another Mac: the first time, right-click it > Open.

Running the script directly instead also works: double-click on Windows, or python3 tcg_price_checker.py on a Mac.

  * Every sealed listing (product types Box / Pack / Tin by default; singles are never checked) is matched
    automatically to a TCGplayer sealed product using tcgcsv.com, TCGplayer's prices republished once a day.
  * Status: URGENT / DRIFTING = our price is that far from TCGplayer (percentages set in Settings),
    CHECK MATCH = please confirm the TCGplayer product, plus cost, margin, presale and fast-moving flags.
  * Choices people make in the window (confirmed matches, hidden products, typed-in live prices, settings)
    are saved in products.json next to this file. cache/ and reports/ are created here too.
  * Shopify login comes from the shopify: section of a config.yaml (store_url + client_id/client_secret,
    or admin_api_token). You choose the file the first time (and can change it in Settings); it's never
    searched for automatically, and no passwords are stored in this script or the app.

Read-only: it only reads from Shopify and tcgcsv, and never changes anything in the shop.

Command line (optional):  py tcg_price_checker.py --cli [--shopify-csv export.csv]
"""
import argparse
import concurrent.futures as cf
import csv
import datetime as dt
import html
import json
import math
import os
import queue
import re
import ssl
import sys
import threading
import time
import traceback
import unicodedata
import urllib.parse
import urllib.request
import webbrowser
from pathlib import Path

def app_folder():
    """Where products.json, cache/ and reports/ live: next to the app, so moving the folder moves everything.

    Works for the plain script, a packaged Windows .exe and a Mac .app (the folder holding the .app).
    Falls back to the user's app-data folder when that place can't be written to (e.g. Program Files, or a
    Mac app run straight from Downloads, which macOS starts from a hidden read-only copy).
    """
    if getattr(sys, "frozen", False):
        exe = Path(sys.executable).resolve()
        folder = exe.parents[3] if ".app/Contents/MacOS" in exe.as_posix() else exe.parent
    else:
        folder = Path(__file__).resolve().parent
    try:
        if "AppTranslocation" in folder.as_posix():
            raise OSError("read-only copy")
        probe = folder / ".write_test"
        probe.write_text("ok")
        probe.unlink()
        return folder
    except OSError:
        if sys.platform == "darwin":
            fallback = Path.home() / "Library" / "Application Support" / "TCG Price Checker"
        elif sys.platform == "win32":
            fallback = Path(os.environ.get("APPDATA", Path.home())) / "TCG Price Checker"
        else:
            fallback = Path.home() / ".tcg_price_checker"
        fallback.mkdir(parents=True, exist_ok=True)
        return fallback


HERE = app_folder()
TCGCSV = "https://tcgcsv.com/tcgplayer"
USER_AGENT = "shop-price-check/2.0"
SHOPIFY_API_VERSION = os.environ.get("SHOPIFY_API_VERSION", "2026-07")
PRESALE_WORDS = ("presale", "pre-sale", "preorder", "pre-order")
SINGLE_CARD_FIELDS = {"Rarity", "Number"}
POS_MARK = re.compile(r"\(\s*POS\s*\)", re.I)  # shopfront marker; can appear anywhere in a title
TAG_ORDER = {"URGENT": 0, "DRIFTING": 1, "CHECK MATCH": 2, "OK": 3, "SELF-PRICED": 4, "NO PRICE": 5,
             "NO MATCH": 6, "NO DATA": 7}
INDEX_VERSION = 1
FIELD_NAMES = {"marketPrice": "TCGplayer Market Price", "lowPrice": "TCGplayer lowest listing"}
RARE_WORD_WEIGHT = 5.5  # word weight (idf) above which a word names something specific

DEFAULT_SETTINGS = {
    "drift_pct": 3,
    "urgent_pct": 10,
    "presale_drift_pct": 3,
    "presale_urgent_pct": 10,
    "tcg_price_field": "marketPrice",
    "sealed_types": ["Box", "Pack", "Tin"],
    "include_drafts": False,
    "ignore_words": ["panini", "topps", "upper deck", "bowman", "donruss", "leaf", "keepsake", "hobby box",
                     "heat seeker", "breaker edition"],
    "self_priced_words": ["damaged"],
    "auto_match_score": 0.75,
    "check_match_score": 0.35,
    # an automatic match this far from our price is more likely the wrong product: ask a person
    "auto_match_max_diff_pct": 75,
    # sets released this recently (and presale items) are flagged fast-moving: tcgcsv is a daily snapshot
    "new_release_days": 30,
    # TCGplayer games to match against (tcgcsv category ids)
    "tcg_categories": [1, 2, 3, 85, 68, 79, 86, 90, 21, 66, 71, 89, 76, 91, 93, 62, 63, 80, 81],
}

# Matches already checked by hand; used to start products.json the first time this runs somewhere new.
ASCENDED_HEROES_EX_BOXES = [{"category": 3, "group": 24541, "product": p} for p in (672733, 672734, 672735)]
DEFAULT_OVERRIDES = [
    {"shopify_title": "Pokemon Mega Evolution - Ascended Heroes ex Box (Damaged Package)",
     "tcg": ASCENDED_HEROES_EX_BOXES,
     "note": "Damaged package - priced in-house; TCGplayer sealed ex Box average shown for reference only"},
    {"shopify_title": "Pokemon Mega Evolution - Ascended Heroes ex Box", "tcg": ASCENDED_HEROES_EX_BOXES,
     "note": "Average of Meganium / Emboar / Feraligatr ex Box (we ship whichever is needed)"},
    {"shopify_title": "Riftbound: League of Legends TCG - Showdown Decks: Evelynn vs Seraphine (RAD)",
     "tcg": [{"category": 89, "group": 24819, "product": 711368}]},
    {"shopify_title": "Yu-Gi-Oh! - Beyond the Brave Booster Pack [1st Edition]",
     "tcg": [{"category": 2, "group": 24815, "product": 711264}]},
    {"shopify_title": "Magic: The Gathering - Reality Fracture Collector Booster Pack",
     "tcg": [{"category": 1, "group": 24684, "product": 692982}]},
    {"shopify_title": "CookieRun Braverse TCG: Festival Arena Booster Pack",
     "tcg": [{"category": 90, "group": 24886, "product": 718118}]},
]


# ---------------------------------------------------------------- helpers

def _ssl_context():
    """Normal certificate checking. Python from python.org on a Mac has no certificates until its
    'Install Certificates' step is run, so also trust the Mac's own list (/etc/ssl/cert.pem)."""
    ctx = ssl.create_default_context()
    if sys.platform == "darwin" and Path("/etc/ssl/cert.pem").exists():
        ctx.load_verify_locations("/etc/ssl/cert.pem")
    return ctx


SSL_CONTEXT = _ssl_context()


def http_open(req, timeout=60):
    return urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT)


def http_json(url, data=None, headers=None):
    req = urllib.request.Request(url, data=data, headers={"User-Agent": USER_AGENT, **(headers or {})})
    with http_open(req) as resp:
        return json.load(resp)


def normalize_title(title):
    """Drop our internal markers so POS and online listings match the same entry."""
    t = POS_MARK.sub(" ", title or "")
    return re.sub(r"\s+", " ", t).strip().lower()


def is_pos(title):
    return bool(POS_MARK.search(title or ""))


def is_presale_text(text):
    text = (text or "").lower()
    return any(w in text for w in PRESALE_WORDS)


def to_float(value):
    try:
        return float(str(value).replace("$", "").replace(",", "").strip())
    except (TypeError, ValueError):
        return None


def is_sealed(product):
    return not any(e.get("name") in SINGLE_CARD_FIELDS for e in product.get("extendedData") or [])


def money(v):
    return "" if v is None else f"{'-' if v < 0 else ''}${abs(v):,.2f}"


def pct(v):
    return "" if v is None else f"{v:+.1f}%"


def load_config(path):
    if Path(path).exists():
        config = json.loads(Path(path).read_text(encoding="utf-8"))
    else:  # first run on this computer
        config = {"overrides": json.loads(json.dumps(DEFAULT_OVERRIDES))}
    config["settings"] = {**DEFAULT_SETTINGS, **config.get("settings", {})}
    config["overrides"] = config.get("overrides", config.pop("products", []))
    return config


def save_config(config, path):
    path = Path(path)
    if path.exists():
        path.with_suffix(".json.bak").write_text(path.read_text(encoding="utf-8"), encoding="utf-8")
    path.write_text(json.dumps(config, indent=2, ensure_ascii=False), encoding="utf-8")


# ---------------------------------------------------------------- word matching

STOPWORDS = {"the", "of", "and", "a", "an", "tcg", "ccg", "card", "cards", "game", "trading", "official", "for",
             "with", "x"}
PHRASES = [  # applied to both sides so different wording lines up
    (r"\byu gi oh\b", "yugioh"),
    (r"\bbooster display\b", "booster box"),
    (r"\bbooster pack\b", "booster"),
    (r"\betb\b", "elite trainer box"),
    (r"\bjapan\b", "japanese"),
    (r"\bfirst edition\b", "1st edition"),
    (r"\bsecond edition\b", "2nd edition"),
    (r"\bvol\b", "volume"),
    (r"\bpokemon center\b", "pokemoncenter"),
    (r"\b(bundle|deck|tin|pack|kit|blister|collection|chest|case)s\b", r"\1"),
    (r"\bboxes\b", "box"),
]
# Our own notes in titles: (POS), (Damaged...), **Tear in Plastic**, (LiveStream Only), presale markers
SHOPIFY_NOISE = re.compile(r"\((?:pos|sealed|damaged[^)]*|[^)]*\bonly)\)|\*\*.*?\*\*|\*[^*]*damaged[^*]*\*|\bpre-?sale\b|\bpre-?order\b",
                           re.I)
# Words that make a different product: a "1st Edition" or Japanese listing must not auto-match one without them.
QUALIFIERS = {"japanese", "korean", "chinese", "german", "french", "italian", "spanish", "portuguese", "russian",
              "1st", "2nd", "unlimited", "sleeved",
              # product types: a "Booster Bundle" must not auto-match a "Booster Pack"
              "bundle", "box", "case", "tin", "deck", "blister", "collection", "kit", "chest", "pack"}
# Pokemon set codes on TCGplayer ("SV10: Destined Rivals") -> the series name we use in titles
POKEMON_SERIES = {"sv": "scarlet violet", "swsh": "sword shield", "me": "mega evolution", "sm": "sun moon",
                  "bw": "black white", "xy": "xy", "dp": "diamond pearl", "hgss": "heartgold soulsilver"}


def words(text):
    t = unicodedata.normalize("NFKD", text or "").encode("ascii", "ignore").decode().lower()
    t = t.replace("&", " and ")
    t = re.sub(r"['’`]", "", t)
    t = re.sub(r"[^a-z0-9]+", " ", t)
    for pat, rep in PHRASES:
        t = re.sub(pat, rep, t)
    return {w for w in t.split() if w not in STOPWORDS}


# ---------------------------------------------------------------- tcgcsv sealed index

def release_date(group):
    """A set's real release date, or "" when tcgcsv only has a fetch timestamp (those aren't midnight)."""
    published = group.get("publishedOn") or ""
    return published[:10] if published[10:19] == "T00:00:00" else ""


class TcgIndex:
    """Every sealed TCGplayer product in the chosen games, cached on disk and refreshed when sets change."""

    def __init__(self, cache_dir):
        self.path = Path(cache_dir) / "tcg_index.json"
        self.data = {"version": INDEX_VERSION, "categories": {}, "groups": {}}
        if self.path.exists():
            try:
                loaded = json.loads(self.path.read_text(encoding="utf-8"))
                if loaded.get("version") == INDEX_VERSION:
                    self.data = loaded
            except ValueError:
                pass
        self._prices = {}
        self._built = False
        # last price seen per product and field: {"cat/group/id": {"marketPrice": [price, "2026-10-27"], ...}}
        self.history_path = Path(cache_dir) / "last_prices.json"
        try:
            self.history = json.loads(self.history_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            self.history = {}
        self.snapshot_date = ""  # date of the tcgcsv snapshot being used, set by PriceChecker.run

    def category_list(self):
        return http_json(f"{TCGCSV}/categories")["results"]

    def refresh(self, category_ids, progress=None):
        """Fetch new/changed sets. First run downloads everything (about a minute)."""
        cats = {c["categoryId"]: c for c in self.category_list()}
        todo = []
        for cid in category_ids:
            if cid not in cats:
                continue
            self.data["categories"][str(cid)] = {"name": cats[cid]["name"],
                                                 "display": cats[cid].get("displayName") or ""}
            try:
                groups = http_json(f"{TCGCSV}/{cid}/groups")["results"]
            except Exception:  # category with no groups yet (tcgcsv returns a 404 XML page)
                groups = []
            for g in groups:
                key = f"{cid}/{g['groupId']}"
                cached = self.data["groups"].get(key)
                if not cached or cached.get("modifiedOn") != g.get("modifiedOn"):
                    todo.append((cid, g))
                else:
                    cached["published"] = release_date(g)

        def fetch(job):
            cid, g = job
            try:
                products = http_json(f"{TCGCSV}/{cid}/{g['groupId']}/products")["results"]
            except Exception:
                products = []
            sealed = []
            for p in products:
                if is_sealed(p):
                    pre = p.get("presaleInfo") or {}
                    sealed.append({"id": p["productId"], "name": p["name"], "url": p.get("url"),
                                   "presale": bool(pre.get("isPresale")),
                                   "release": (pre.get("releasedOn") or "")[:10]})
            return f"{cid}/{g['groupId']}", {"category": cid, "group": g["groupId"], "name": g["name"],
                                             "abbr": g.get("abbreviation") or "",
                                             "modifiedOn": g.get("modifiedOn"),
                                             "published": release_date(g), "products": sealed}

        with cf.ThreadPoolExecutor(8) as ex:
            for i, (key, value) in enumerate(ex.map(fetch, todo), 1):
                self.data["groups"][key] = value
                if progress and (i % 25 == 0 or i == len(todo)):
                    progress(f"Updating TCGplayer catalogue: {i} of {len(todo)} sets")
        # always save: release dates may have changed even when no set needed downloading
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(self.data), encoding="utf-8")
        self._built = False

    def _build(self):
        """Word lists + inverted index for matching."""
        self.products = []
        for g in self.data["groups"].values():
            cat = self.data["categories"].get(str(g["category"]), {})
            set_words = words(g["name"])
            context = set_words | words(cat.get("name", "")) | words(cat.get("display", ""))
            if g["abbr"]:
                context.add(g["abbr"].lower())
            code = re.match(r"([A-Za-z]+)\d*\s*:", g["name"])
            if code and code.group(1).lower() in POKEMON_SERIES:
                context |= words(POKEMON_SERIES[code.group(1).lower()])
            for p in g["products"]:
                name = words(p["name"])
                # Words that only repeat the set name ("Universes Beyond: ...") shouldn't count as extras.
                own = (name - set_words) or name
                self.products.append({**p, "category": g["category"], "group": g["group"], "set": g["name"],
                                      "set_released": g.get("published", ""),
                                      "game": cat.get("display") or cat.get("name", ""),
                                      "name_words": own, "all_words": name | context})
        df = {}
        self.postings = {}
        for i, p in enumerate(self.products):
            for w in p["all_words"]:
                df[w] = df.get(w, 0) + 1
                self.postings.setdefault(w, []).append(i)
        n = max(len(self.products), 1)
        self.idf = {w: math.log(n / c) + 1 for w, c in df.items()}
        self._built = True

    def weight(self, w):
        return self.idf.get(w, 1.0)  # words TCGplayer never uses are probably our own noise

    def score(self, query, p):
        if not query:
            return 0.0
        wq = sum(self.weight(w) for w in query)
        wn = sum(self.weight(w) for w in p["name_words"]) or 1
        recall = sum(self.weight(w) for w in query & p["all_words"]) / wq          # how much of our title is explained
        precision = sum(self.weight(w) for w in p["name_words"] & query) / wn       # extra words like "Case" or "Display" hurt
        return recall * precision

    def candidates(self, text, limit=10):
        """Best TCGplayer sealed products for a Shopify title, best first: [(score, product), ...]."""
        if not self._built:
            self._build()
        query = words(SHOPIFY_NOISE.sub(" ", text))
        seeds = sorted((w for w in query if w in self.postings), key=self.weight, reverse=True)[:3]
        pool = set()
        for w in seeds:
            pool.update(self.postings[w])
        scored = sorted(((self.score(query, self.products[i]), self.products[i]) for i in pool),
                        key=lambda sp: sp[0], reverse=True)
        return scored[:limit]

    def product(self, category, group, product_id):
        g = self.data["groups"].get(f"{category}/{group}")
        if not g:
            return None
        return next(({**p, "category": category, "group": group, "set": g["name"], "set_released": g.get("published", "")}
                     for p in g["products"] if p["id"] == product_id), None)

    def load_prices(self, keys, progress=None):
        """Fetch price files for the given (category, group) pairs, in parallel."""
        todo = [k for k in set(keys) if k not in self._prices]

        def fetch(key):
            try:
                rows = http_json(f"{TCGCSV}/{key[0]}/{key[1]}/prices")["results"]
            except Exception:
                rows = []
            by_id = {}
            for r in rows:
                by_id.setdefault(r["productId"], []).append(r)
            return key, by_id

        with cf.ThreadPoolExecutor(8) as ex:
            for i, (key, value) in enumerate(ex.map(fetch, todo), 1):
                self._prices[key] = value
                if progress and (i % 25 == 0 or i == len(todo)):
                    progress(f"Loading TCGplayer prices: {i} of {len(todo)} sets")
        if todo and self.snapshot_date:
            self._remember(todo)

    @staticmethod
    def _row(rows):
        # sealed product is "Normal"; fall back to whatever subtype exists
        return next((r for r in rows if r.get("subTypeName") == "Normal"), rows[0] if rows else {})

    def _remember(self, keys):
        for key in keys:
            for product_id, rows in self._prices.get(key, {}).items():
                row = self._row(rows)
                entry = self.history.setdefault(f"{key[0]}/{key[1]}/{product_id}", {})
                for f in ("marketPrice", "lowPrice"):
                    if row.get(f) is not None:
                        entry[f] = [row[f], self.snapshot_date]
        try:
            self.history_path.parent.mkdir(parents=True, exist_ok=True)
            self.history_path.write_text(json.dumps(self.history), encoding="utf-8")
        except OSError:
            pass

    def price(self, category, group, product_id, field):
        """Returns (price, as_of, cheapest listing). Only the chosen field is used (Market Price by default).

        as_of is "" for today's snapshot, or the date of the last snapshot that had a price: tcgcsv leaves
        out products with no listings, but TCGplayer still shows their last Market Price.
        """
        row = self._row(self._prices.get((category, group), {}).get(product_id, []))
        if row.get(field) is not None:
            return row[field], "", row.get("lowPrice")
        seen = self.history.get(f"{category}/{group}/{product_id}", {}).get(field)
        if seen:
            return seen[0], seen[1], row.get("lowPrice")
        return None, "", row.get("lowPrice")

    @staticmethod
    def last_updated():
        req = urllib.request.Request("https://tcgcsv.com/last-updated.txt", headers={"User-Agent": USER_AGENT})
        with http_open(req, timeout=30) as resp:
            return resp.read().decode().strip()


# ---------------------------------------------------------------- shopify

def shop_domain(store_url):
    """Accept 'my-store', 'my-store.myshopify.com', 'https://...', or 'admin.shopify.com/store/my-store'."""
    store = re.sub(r"^https?://", "", store_url.strip()).rstrip("/")
    m = re.match(r"admin\.shopify\.com/store/([^/]+)", store)
    if m:
        store = m.group(1)
    store = store.split("/")[0]
    return store if "." in store else store + ".myshopify.com"


class SetupError(Exception):
    """Something the user needs to fix (credentials, files)."""


def read_yaml_section(text, section):
    """The simple `key: "value"` lines under one top-level section of a YAML file.

    Uses PyYAML when it's installed; otherwise this small reader is enough for the config.yaml layout,
    so nobody has to install anything.
    """
    try:
        import yaml
        return (yaml.safe_load(text) or {}).get(section) or {}
    except ImportError:
        pass
    values, inside = {}, False
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if not line[0].isspace():  # a new top-level section
            inside = line.split(":", 1)[0].strip() == section
            continue
        if not inside or line.startswith(" " * 4):  # skip nested sub-sections
            continue
        key, _, value = line.strip().partition(":")
        value = value.strip()
        if value and value[0] in "\"'":
            value = value[1:].split(value[0], 1)[0]
        else:
            value = value.split(" #", 1)[0].strip()
        values[key.strip()] = value
    return values


def check_credentials_file(path):
    """None if this looks like a usable Shopify login file, otherwise what's wrong in plain words."""
    if not path:
        return "No Shopify login file chosen yet. Open Settings and choose your config.yaml."
    path = Path(path)
    if not path.is_file():
        return f"The Shopify login file can't be found:\n{path}\n\nOpen Settings and choose it again."
    try:
        cfg = read_yaml_section(path.read_text(encoding="utf-8"), "shopify")
    except (OSError, UnicodeDecodeError, ValueError) as e:
        return f"Couldn't read {path.name}: {e}"
    cfg = {k: str(v).strip() for k, v in (cfg or {}).items() if v}
    if not cfg:
        return f"{path.name} has no filled-in 'shopify:' section."
    if not cfg.get("store_url"):
        return f"{path.name}: the shopify: section needs a store_url."
    if not (cfg.get("admin_api_token") or cfg.get("app_automation_token")
            or (cfg.get("client_id") and cfg.get("client_secret"))):
        return f"{path.name}: the shopify: section needs client_id and client_secret (or an admin_api_token)."
    return None


def shopify_credentials(config_path):
    """Return (store, token) from env vars, else the shopify: section of the shared config.yaml.

    Token order: admin_api_token, then a client-credentials exchange with client_id/client_secret,
    then app_automation_token. Returns None when nothing usable is configured.
    """
    if os.environ.get("SHOPIFY_STORE") and os.environ.get("SHOPIFY_TOKEN"):
        return shop_domain(os.environ["SHOPIFY_STORE"]), os.environ["SHOPIFY_TOKEN"]
    if not config_path or not Path(config_path).exists():
        return None
    cfg = read_yaml_section(Path(config_path).read_text(encoding="utf-8"), "shopify")
    cfg = {k: str(v).strip() for k, v in cfg.items() if v}
    if not cfg.get("store_url"):
        return None
    store = shop_domain(cfg["store_url"])
    if cfg.get("admin_api_token"):
        return store, cfg["admin_api_token"]
    if cfg.get("client_id") and cfg.get("client_secret"):
        # Dev Dashboard apps installed on our own store can swap id/secret for a 24h Admin API token.
        body = urllib.parse.urlencode({"grant_type": "client_credentials", "client_id": cfg["client_id"],
                                       "client_secret": cfg["client_secret"]}).encode()
        try:
            data = http_json(f"https://{store}/admin/oauth/access_token", data=body,
                             headers={"Content-Type": "application/x-www-form-urlencoded"})
            return store, data["access_token"]
        except Exception as e:
            if not cfg.get("app_automation_token"):
                raise SetupError(f"Shopify login failed: {e}")
            print(f"Client-credentials login failed ({e}); using app_automation_token", file=sys.stderr)
    if cfg.get("app_automation_token"):
        return store, cfg["app_automation_token"]
    return None


def shopify_from_api(store, token, progress=None):
    """Yield one record per variant of every product in our shop."""
    url = f"https://{store}/admin/api/{SHOPIFY_API_VERSION}/graphql.json"
    query = """
    query($cursor: String, $size: Int!) {
      products(first: $size, after: $cursor) {
        pageInfo { hasNextPage endCursor }
        nodes {
          title status tags productType
          variants(first: 50) { nodes { title price compareAtPrice sku inventoryQuantity COST } }
        }
      }
    }"""
    cost_field = "inventoryItem { unitCost { amount } }"  # "Cost per item"; needs the read_inventory scope
    cursor, count, size, tries = None, 0, 100, 0
    while True:
        body = json.dumps({"query": query.replace("COST", cost_field),
                           "variables": {"cursor": cursor, "size": size}}).encode()
        data = http_json(url, data=body, headers={"X-Shopify-Access-Token": token, "Content-Type": "application/json"})
        if data.get("errors"):
            text = json.dumps(data["errors"])
            tries += 1
            if tries > 8:
                raise SetupError(f"Shopify API error: {data['errors']}")
            if "THROTTLED" in text:
                time.sleep(2)
            elif "MAX_COST_EXCEEDED" in text and size > 10:
                size //= 2
            elif cost_field and ("ACCESS_DENIED" in text or "inventoryItem" in text):
                cost_field = ""  # app can't see costs: carry on without them
            else:
                raise SetupError(f"Shopify API error: {data['errors']}")
            continue
        tries = 0
        page = data["data"]["products"]
        for p in page["nodes"]:
            for v in p["variants"]["nodes"]:
                yield {
                    "title": p["title"],
                    "variant": "" if v["title"] == "Default Title" else v["title"],
                    "price": to_float(v["price"]),
                    "compare_at": to_float(v.get("compareAtPrice")),
                    "cost": to_float(((v.get("inventoryItem") or {}).get("unitCost") or {}).get("amount")),
                    "stock": v.get("inventoryQuantity"),
                    "status": p.get("status", ""),
                    "type": p.get("productType") or "",
                    "tags": ", ".join(p.get("tags") or []),
                }
        count += len(page["nodes"])
        if progress:
            progress(f"Reading Shopify products: {count}")
        if not page["pageInfo"]["hasNextPage"]:
            break
        cursor = page["pageInfo"]["endCursor"]


def shopify_from_csv(path):
    """Read Shopify's product export (variant rows inherit the title via Handle)."""
    first_by_handle = {}
    with open(path, newline="", encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            row = {k.strip().lower(): (v or "").strip() for k, v in row.items() if k}
            handle = row.get("handle", "")
            if handle and row.get("title"):
                first_by_handle[handle] = row
            parent = first_by_handle.get(handle, row)
            title = row.get("title") or parent.get("title", "")
            price = to_float(row.get("variant price") or row.get("price"))
            if not title or price is None:
                continue
            variant = " / ".join(v for v in (row.get("option1 value"), row.get("option2 value")) if v and v != "Default Title")
            yield {
                "title": title,
                "variant": variant,
                "price": price,
                "compare_at": to_float(row.get("variant compare at price") or row.get("compare at price")),
                "cost": to_float(row.get("cost per item")),
                "stock": row.get("variant inventory qty") or None,
                "status": (parent.get("status") or "active").upper(),
                "type": parent.get("type") or parent.get("product type") or "",
                "tags": parent.get("tags", ""),
            }


def is_tracked(item, settings):
    """Sealed product we sell: right product type, active (unless drafts wanted), not on the ignore list."""
    if item.get("type", "").lower() not in {t.lower() for t in settings["sealed_types"]}:
        return False
    if not settings.get("include_drafts") and item.get("status", "").upper() not in ("ACTIVE", ""):
        return False
    return not has_any_word(item["title"], settings.get("ignore_words", []))


def has_any_word(text, phrases):
    """Whole-word match, so "leaf" skips Leaf sports cards but not Leafeon."""
    return any(re.search(rf"(?<![a-z0-9]){re.escape(p.strip().lower())}(?![a-z0-9])", (text or "").lower())
               for p in phrases if p.strip())


# ---------------------------------------------------------------- comparison

def classify(diff_pct, presale, settings):
    drift = settings["presale_drift_pct"] if presale else settings["drift_pct"]
    urgent = settings["presale_urgent_pct"] if presale else settings["urgent_pct"]
    if abs(diff_pct) >= urgent:
        return "URGENT"
    if abs(diff_pct) >= drift:
        return "DRIFTING"
    return "OK"


def parse_time(text):
    """tcgcsv's '2026-10-27T20:05:13+0000' or our own isoformat -> aware datetime (None if blank)."""
    if not text:
        return None
    text = re.sub(r"([+-]\d\d)(\d\d)$", r"\1:\2", text.strip())
    t = dt.datetime.fromisoformat(text)
    return t if t.tzinfo else t.replace(tzinfo=dt.timezone.utc)


def find_live_price(config, title, variant, tcg_updated):
    """A price someone typed in from TCGplayer's site, if it's newer than the tcgcsv snapshot.
    Pass tcg_updated="" when the snapshot has no price for the product, so the typed price keeps counting."""
    key, variant = normalize_title(title), (variant or "").lower()
    snapshot = parse_time(tcg_updated)
    for e in config.get("live_prices", []):
        if normalize_title(e["shopify_title"]) == key and (e.get("variant") or "").lower() == variant:
            if snapshot is None or parse_time(e["entered"]) > snapshot:
                return e
    return None


def set_live_price(config, title, variant, price):
    """Save (or with price None, clear) a hand-entered TCGplayer price for one listing."""
    key, variant = normalize_title(title), variant or ""
    config["live_prices"] = [
        e for e in config.get("live_prices", [])
        if not (normalize_title(e["shopify_title"]) == key and (e.get("variant") or "") == variant)]
    if price is not None:
        config["live_prices"].append({"shopify_title": POS_MARK.sub("", title).strip(), "variant": variant,
                                      "price": price, "entered": dt.datetime.now(dt.timezone.utc).isoformat()})


def margin(price, cost):
    """Gross margin as % of price, or None when either is unknown."""
    return (price - cost) / price * 100 if price and cost else None


def find_override(config, title, variant):
    """Saved match for this listing: title+variant first, then title only. (POS) is ignored."""
    key = normalize_title(title)
    title_only = None
    for o in config["overrides"]:
        if normalize_title(o["shopify_title"]) != key:
            continue
        if o.get("variant"):
            if o["variant"].lower() == (variant or "").lower():
                return o
        elif title_only is None:
            title_only = o
    return title_only


def set_override(config, title, variant, **fields):
    """Save (or with no fields, remove) the override for exactly this title/variant."""
    key, variant = normalize_title(title), variant or ""
    config["overrides"] = [o for o in config["overrides"]
                           if not (normalize_title(o["shopify_title"]) == key and (o.get("variant") or "") == variant)]
    if fields:
        entry = {"shopify_title": POS_MARK.sub("", title).strip()}
        if variant:
            entry["variant"] = variant
        entry.update(fields)
        config["overrides"].append(entry)


def match_listing(config, index, item):
    """Returns (refs, how, score, alternatives). how: 'saved', 'auto', 'check', 'none', 'ignored'."""
    settings = config["settings"]
    override = find_override(config, item["title"], item["variant"])
    if override:
        if override.get("ignore"):
            return [], "ignored", None, []
        refs = [index.product(t["category"], t["group"], t["product"]) for t in override.get("tcg", [])]
        refs = [r for r in refs if r]
        if refs or override.get("self_priced"):
            return refs, "saved", None, []
    text = f"{item['title']} {item['variant']}"
    cands = index.candidates(text, limit=5)
    if not cands or cands[0][0] < settings["check_match_score"]:
        return [], "none", cands[0][0] if cands else None, cands
    best_score, best = cands[0]
    runner_up = cands[1][0] if len(cands) > 1 else 0
    query = words(SHOPIFY_NOISE.sub(" ", text))
    same_kind = query & QUALIFIERS <= best["all_words"]
    # a rare word of ours (e.g. "Nightfall") missing from their product usually means a different product
    # (set codes and years like "OP-14" or "2026" are ours, so words with digits don't count)
    missing_rare = any(index.weight(w) >= RARE_WORD_WEIGHT and not re.search(r"\d", w)
                       for w in query - best["all_words"])
    confident = (best_score >= settings["auto_match_score"] and best_score - runner_up >= 0.05
                 and same_kind and not missing_rare)
    return [best], ("auto" if confident else "check"), best_score, cands


def build_rows(config, shopify_items, index, progress=None, tcg_updated=""):
    settings = config["settings"]
    field = settings.get("tcg_price_field", "marketPrice")
    listings = [i for i in shopify_items if is_tracked(i, settings)]
    new_since = (dt.date.today() - dt.timedelta(days=settings.get("new_release_days", 30))).isoformat()

    matched = []
    for n, item in enumerate(listings, 1):
        matched.append((item, *match_listing(config, index, item)))
        if progress and n % 100 == 0:
            progress(f"Matching products: {n} of {len(listings)}")
    index.load_prices([(r["category"], r["group"]) for _, refs, *_ in matched for r in refs], progress)

    rows = []
    for item, refs, how, score, cands in matched:
        if how == "ignored":
            continue
        override = find_override(config, item["title"], item["variant"]) or {}
        prices = [index.price(r["category"], r["group"], r["id"], field) for r in refs]
        values = [p[0] for p in prices if p[0] is not None]
        snapshot_price = market = sum(values) / len(values) if values else None
        as_of = max((p[1] for p in prices if p[0] is not None and p[1]), default="")  # "" = today's snapshot
        # a typed price is replaced once a newer snapshot has today's price; otherwise it keeps counting
        live = find_live_price(config, item["title"], item["variant"],
                               tcg_updated if values and not as_of else "")
        if live:
            market = live["price"]
        ours = item["price"]
        cost = item.get("cost") or None  # "Cost per item"; 0 means it was never filled in
        diff = diff_amt = None
        if ours and market:
            diff_amt = ours - market
            diff = diff_amt / market * 100
        presale = (bool(override.get("presale")) or any(r.get("presale") for r in refs)
                   or is_presale_text(item["tags"]) or is_presale_text(item["title"]))
        self_priced = bool(override.get("self_priced")) or has_any_word(item["title"], settings.get("self_priced_words", []))

        if not ours:
            tag = "NO DATA"
        elif self_priced:
            tag = "SELF-PRICED"
        elif how == "none":
            tag = "NO MATCH"
        elif how == "check" or (how == "auto" and diff is not None
                                and abs(diff) >= settings.get("auto_match_max_diff_pct", 75)):
            tag = "CHECK MATCH"
        elif market is None:
            tag = "NO PRICE"
        else:
            tag = classify(diff, presale, settings)

        rows.append({
            "shopify_title": item["title"],
            "variant": item["variant"],
            "channel": "POS" if is_pos(item["title"]) else "Online",
            "status": item["status"],
            "type": item.get("type", ""),
            "stock": item["stock"],
            "our_price": ours,
            "compare_at": item["compare_at"],
            "cost": cost,
            "margin_pct": margin(ours, cost),            # profit at our price, % of price
            "tcg_margin_pct": margin(market, cost),      # profit if we priced at TCGplayer
            "below_cost": bool(cost and market is not None and market < cost),
            "tcg_refs": [{"category": r["category"], "group": r["group"], "product": r["id"]} for r in refs],
            "tcg_name": " | ".join(r["name"] for r in refs),
            "tcg_set": " | ".join(dict.fromkeys(r["set"] for r in refs)),
            "tcg_urls": [r["url"] for r in refs if r.get("url")],
            "tcg_price": market,
            "tcg_low": min((p[2] for p in prices if p[2] is not None), default=None),
            "source": ("price typed in from TCGplayer's site" if live else
                       (FIELD_NAMES.get(field, field) + (f" (average of {len(values)})" if len(values) > 1 else "")
                        + (f", last seen {as_of} (no listings since)" if as_of else " from the daily snapshot"))
                       if values else ""),
            "price_as_of": "" if live else as_of,
            "match": {"saved": "Confirmed", "auto": "Automatic", "check": "Needs check", "none": "Not found"}[how],
            "match_score": score,
            "diff_amt": diff_amt,
            "diff_pct": diff,
            "presale": presale,
            "release": next((r["release"] for r in refs if r.get("release")), ""),
            # presale / just released: TCGplayer prices can move a lot between daily snapshots
            "fast_moving": presale or any((r.get("set_released") or "") >= new_since for r in refs),
            "snapshot_price": snapshot_price,
            "live_entered": live["entered"] if live else "",
            "tag": tag,
            "note": override.get("note", ""),
        })
    rows.sort(key=lambda r: (TAG_ORDER[r["tag"]], not r["presale"], -abs(r["diff_pct"] or 0), r["shopify_title"]))
    return rows


class PriceChecker:
    """Holds one session's data so the GUI can re-run matching without downloading again."""

    def __init__(self, config_path=HERE / "products.json", credentials_path=None, out_dir=HERE / "reports",
                 cache_dir=HERE / "cache"):
        self.config_path = Path(config_path)
        self.out_dir = Path(out_dir)
        self.config = load_config(self.config_path)
        saved = self.config["settings"].get("credentials_file")
        chosen = credentials_path or saved  # picked by hand in the window (or --credentials); never guessed
        self.credentials_path = Path(chosen) if chosen else None
        self.index = TcgIndex(cache_dir)
        self.shopify_items = None
        self.rows = []
        self.tcg_updated = ""

    def save(self):
        save_config(self.config, self.config_path)

    def run(self, progress=print, shopify_csv=None):
        progress("Connecting to Shopify…")
        if shopify_csv:
            self.shopify_items = list(shopify_from_csv(shopify_csv))
        else:
            problem = check_credentials_file(self.credentials_path)
            if problem and not os.environ.get("SHOPIFY_TOKEN"):
                raise SetupError(problem)
            creds = shopify_credentials(self.credentials_path)
            if not creds:
                raise SetupError(f"No Shopify login found. Fill in store_url and client_id/client_secret in the "
                                 f"shopify: section of {self.credentials_path}")
            self.shopify_items = list(shopify_from_api(*creds, progress=progress))
        progress("Checking TCGplayer catalogue for new sets…")
        self.index.refresh(self.config["settings"]["tcg_categories"], progress)
        self.index._prices = {}  # always re-download prices so a new daily snapshot is picked up
        self.tcg_updated = self.index.last_updated()
        self.index.snapshot_date = self.tcg_updated[:10]
        return self.recompute(progress)

    def snapshot_age(self):
        """('Oct 27, 4:05 PM', hours old) for the tcgcsv snapshot in local time, or (None, None)."""
        t = parse_time(self.tcg_updated)
        if not t:
            return None, None
        local = t.astimezone()
        hours = (dt.datetime.now(dt.timezone.utc) - t).total_seconds() / 3600
        return local.strftime("%b %d, %I:%M %p").replace(" 0", " "), hours

    def recompute(self, progress=None):
        self.rows = build_rows(self.config, self.shopify_items or [], self.index, progress, self.tcg_updated)
        return self.rows

    def recompute_title(self, title):
        """Re-match just the listings with this title (after a saved choice changes)."""
        key = normalize_title(title)
        items = [i for i in self.shopify_items or [] if normalize_title(i["title"]) == key]
        self.rows = [r for r in self.rows if normalize_title(r["shopify_title"]) != key]
        self.rows += build_rows(self.config, items, self.index, tcg_updated=self.tcg_updated)
        self.rows.sort(key=lambda r: (TAG_ORDER[r["tag"]], not r["presale"], -abs(r["diff_pct"] or 0), r["shopify_title"]))

    def search_tcg(self, text, limit=40):
        """TCGplayer sealed products for the match picker, with today's price: [(score, product, price)]."""
        cands = self.index.candidates(text, limit=limit)
        self.index.load_prices([(p["category"], p["group"]) for _, p in cands])
        field = self.config["settings"].get("tcg_price_field", "marketPrice")
        return [(s, p, self.index.price(p["category"], p["group"], p["id"], field)[0]) for s, p in cands]

    def product_types(self):
        """Product types in our shop with listing counts, most common first."""
        counts = {}
        for i in self.shopify_items or []:
            counts[i.get("type") or ""] = counts.get(i.get("type") or "", 0) + 1
        return sorted(counts.items(), key=lambda kv: -kv[1])

    def write_reports(self):
        report_date = dt.date.today().isoformat()
        self.out_dir.mkdir(parents=True, exist_ok=True)
        html_path = self.out_dir / f"price_report_{report_date}.html"
        csv_path = self.out_dir / f"price_report_{report_date}.csv"
        write_html(self.rows, html_path, self.config["settings"], report_date, self.tcg_updated)
        write_csv(self.rows, csv_path)
        return html_path, csv_path


# ---------------------------------------------------------------- output

CSV_COLUMNS = ["tag", "presale", "release", "channel", "shopify_title", "variant", "type", "our_price", "cost",
               "margin_pct", "tcg_price", "tcg_margin_pct", "below_cost", "diff_amt", "diff_pct", "tcg_low", "match",
               "match_score", "tcg_name", "tcg_set", "source", "price_as_of", "snapshot_price", "live_entered", "fast_moving", "status",
               "stock", "note"]


def write_csv(rows, path):
    # diff_amt / diff_pct = our price minus TCGplayer
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(CSV_COLUMNS)
        for r in rows:
            w.writerow([round(r[c], 2) if isinstance(r[c], float) else r[c] for c in CSV_COLUMNS])


def tag_class(tag):
    return re.sub(r"[^a-z]", "", tag.lower())


def write_html(rows, path, settings, report_date, tcg_updated):
    counts = {t: sum(r["tag"] == t for r in rows) for t in TAG_ORDER}
    presale_count = sum(r["presale"] for r in rows)
    body = []
    for r in rows:
        if r["diff_pct"] is None:
            action = ""
        elif r["diff_pct"] > 0:
            action = "We're above TCGplayer"
        else:
            action = "We're below TCGplayer"
        links = " ".join(f'<a href="{html.escape(u)}" target="_blank">TCGplayer</a>' for u in r["tcg_urls"][:1])
        diff_cls = "" if r["diff_pct"] is None else ("up" if r["diff_pct"] > 0 else "down")
        body.append(f"""<tr class="row-{tag_class(r['tag'])}{' row-presale' if r['presale'] else ''}{' row-belowcost' if r['below_cost'] else ''}{' row-fast' if r['fast_moving'] else ''}">
  <td><span class="tag t-{tag_class(r['tag'])}">{r['tag']}</span>{' <span class="tag t-presale">PRESALE</span>' if r['presale'] else ''}{' <span class="tag t-fast" title="Price can move a lot between daily snapshots - check live">⚡ FAST-MOVING</span>' if r['fast_moving'] else ''}</td>
  <td><div class="title">{html.escape(r['shopify_title'])}{(' — ' + html.escape(r['variant'])) if r['variant'] else ''}</div>
      <div class="sub">{r['channel']} · {html.escape(r['type'])}{' · stock ' + str(r['stock']) if r['stock'] not in (None, '') else ''}</div>
      {f'<div class="sub">{html.escape(r["note"])}</div>' if r['note'] else ''}</td>
  <td class="num">{money(r['our_price'])}{f'<div class="sub">was {money(r["compare_at"])}</div>' if r['compare_at'] else ''}</td>
  <td class="num">{money(r['cost'])}{f'<div class="sub">margin {r["margin_pct"]:.0f}%</div>' if r['margin_pct'] is not None else ''}</td>
  <td class="num">{money(r['tcg_price'])}{f'<div class="sub">typed in (snapshot {money(r["snapshot_price"])})</div>' if r['live_entered'] else ''}{f'<div class="sub">low {money(r["tcg_low"])}</div>' if r['tcg_low'] is not None else ''}{f'<div class="sub{" neg" if r["tcg_margin_pct"] < 0 else ""}">margin {r["tcg_margin_pct"]:.0f}%{" · below cost" if r["below_cost"] else ""}</div>' if r['tcg_margin_pct'] is not None else ''}</td>
  <td class="num {diff_cls}"><b>{pct(r['diff_pct'])}</b><div class="sub">{('+' if (r['diff_amt'] or 0) > 0 else '') + money(r['diff_amt']) if r['diff_amt'] is not None else ''}</div><div class="sub">{action}</div></td>
  <td><div>{html.escape(r['tcg_name'] or '—')}</div><div class="sub">{html.escape(r['tcg_set'])}</div>
      <div class="sub">{r['match']}{(' · releases ' + r['release']) if r['presale'] and r['release'] else ''} {links}</div></td>
</tr>""")
    cards = "".join(f'<div class="card"><b class="c-{tag_class(t)}">{counts[t]}</b>{t.title()}</div>'
                    for t in TAG_ORDER if counts[t])
    buttons = "".join(f'<button data-f="{tag_class(t)}">{t.title()}</button>' for t in TAG_ORDER if counts[t])
    page = f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Price Check {report_date}</title>
<style>
:root{{--bg:#f7f7f5;--card:#fff;--fg:#1d1d1b;--muted:#6b6b66;--line:#e4e4df;--red:#c62828;--redbg:#fdecea;--amber:#a15c00;--amberbg:#fff4e0;--green:#2e7d32;--greenbg:#e8f5e9;--blue:#1e4fb8;--bluebg:#e8eefc;--grey:#777;--greybg:#eee}}
@media (prefers-color-scheme:dark){{:root{{--bg:#161615;--card:#1f1f1d;--fg:#ececea;--muted:#9a9a94;--line:#33332f;--red:#ff7b72;--redbg:#3a1a18;--amber:#f0b45a;--amberbg:#3a2a10;--green:#7ccf80;--greenbg:#16301a;--blue:#8fb0ff;--bluebg:#1a2540;--grey:#aaa;--greybg:#2a2a28}}}}
body{{margin:0;background:var(--bg);color:var(--fg);font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif}}
main{{max-width:1300px;margin:0 auto;padding:24px 16px}}
h1{{font-size:22px;margin:0 0 4px}} .meta{{color:var(--muted);margin-bottom:16px}}
.cards{{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:16px}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 16px;min-width:110px}}
.card b{{display:block;font-size:22px}}
.c-urgent{{color:var(--red)}} .c-drifting{{color:var(--amber)}} .c-ok{{color:var(--green)}} .c-checkmatch{{color:var(--blue)}}
.filters{{margin-bottom:10px;display:flex;gap:6px;flex-wrap:wrap}}
.filters button{{border:1px solid var(--line);background:var(--card);color:var(--fg);border-radius:16px;padding:4px 12px;cursor:pointer}}
.filters button.on{{background:var(--fg);color:var(--bg)}}
.wrap{{overflow-x:auto;background:var(--card);border:1px solid var(--line);border-radius:8px}}
table{{border-collapse:collapse;width:100%;min-width:900px}}
th,td{{padding:8px 10px;border-bottom:1px solid var(--line);text-align:left;vertical-align:top}}
th{{font-size:12px;color:var(--muted);font-weight:600;position:sticky;top:0;background:var(--card)}}
.num{{text-align:right;white-space:nowrap}} .sub{{color:var(--muted);font-size:12px}} .title{{font-weight:500}}
.up{{color:var(--red)}} .down{{color:var(--amber)}} .sub.neg{{color:var(--red);font-weight:600}}
.tag{{display:inline-block;font-size:11px;font-weight:700;padding:2px 7px;border-radius:4px;margin:0 4px 4px 0;white-space:nowrap}}
.t-urgent{{background:var(--redbg);color:var(--red)}} .t-drifting{{background:var(--amberbg);color:var(--amber)}}
.t-ok{{background:var(--greenbg);color:var(--green)}} .t-nodata,.t-selfpriced,.t-nomatch,.t-noprice{{background:var(--greybg);color:var(--grey)}}
.t-presale,.t-fast{{background:var(--bluebg);color:var(--blue)}} .t-checkmatch{{background:var(--bluebg);color:var(--blue);outline:1px dashed var(--blue)}}
a{{color:var(--blue)}}
</style></head><body><main>
<h1>Shopify vs TCGplayer — {report_date}</h1>
<div class="meta">{len(rows)} sealed listings · TCGplayer prices are tcgcsv's daily snapshot from {html.escape(tcg_updated)} (UTC) - ⚡ items may have moved since · Diff = our price vs TCGplayer ·
Drifting ≥ {settings['drift_pct']}% / Urgent ≥ {settings['urgent_pct']}% (presale: {settings['presale_drift_pct']}% / {settings['presale_urgent_pct']}%)</div>
<div class="cards">{cards}<div class="card"><b style="color:var(--blue)">{presale_count}</b>Presale</div></div>
<div class="filters"><button class="on" data-f="all">All</button>{buttons}<button data-f="presale">Presale</button><button data-f="belowcost">TCGplayer below our cost</button><button data-f="fast">⚡ Fast-moving</button></div>
<div class="wrap"><table>
<thead><tr><th>Tag</th><th>Shopify product</th><th class="num">Our price</th><th class="num">Cost</th><th class="num">TCGplayer</th><th class="num">Us vs TCG</th><th>TCGplayer match</th></tr></thead>
<tbody>{''.join(body)}</tbody></table></div>
</main>
<script>
document.querySelectorAll('.filters button').forEach(b=>b.onclick=()=>{{
  document.querySelectorAll('.filters button').forEach(x=>x.classList.toggle('on',x===b));
  const f=b.dataset.f;
  document.querySelectorAll('tbody tr').forEach(tr=>{{tr.style.display=(f==='all'||tr.classList.contains('row-'+f))?'':'none';}});
}});
</script></body></html>"""
    path.write_text(page, encoding="utf-8")


# ================================================================ window

import tkinter as tk  # noqa: E402
from tkinter import filedialog, messagebox, simpledialog, ttk  # noqa: E402

FILTERS = [("All", None), ("Urgent", "URGENT"), ("Drifting", "DRIFTING"), ("Check match", "CHECK MATCH"),
           ("OK", "OK"), ("Presale", "presale"), ("⚡ Fast-moving", "fast_moving"), ("Below cost", "below_cost"), ("We price", "SELF-PRICED"),
           ("Not on TCGplayer", "NO MATCH"),
           ("No price", "NO PRICE"), ("No data", "NO DATA")]
ROW_COLORS = {"URGENT": "#fbe3e1", "DRIFTING": "#fff1d6", "CHECK MATCH": "#e3eafc", "OK": "#ffffff",
              "SELF-PRICED": "#f1f1ef", "NO MATCH": "#f1f1ef", "NO PRICE": "#f1f1ef", "NO DATA": "#f1f1ef"}
COLUMNS = [  # id, heading, width, anchor, sort key
    ("tag", "Status", 105, "w", lambda r: TAG_ORDER[r["tag"]]),
    ("flags", "Flags", 72, "center", lambda r: (not r["presale"], not r["fast_moving"])),
    ("product", "Shopify product", 400, "w", lambda r: r["shopify_title"].lower()),
    ("ours", "Our price", 80, "e", lambda r: r["our_price"] or 0),
    ("cost", "Cost", 75, "e", lambda r: r["cost"] or 0),
    ("margin", "Our margin", 85, "e", lambda r: r["margin_pct"] if r["margin_pct"] is not None else -1e9),
    ("tcg", "TCG market", 85, "e", lambda r: r["tcg_price"] or 0),
    ("tcgmargin", "Margin at TCG", 100, "e", lambda r: r["tcg_margin_pct"] if r["tcg_margin_pct"] is not None else -1e9),
    ("diff", "Difference", 85, "e", lambda r: abs(r["diff_pct"] or 0)),
    ("amt", "$ diff", 75, "e", lambda r: abs(r["diff_amt"] or 0)),
    ("match", "TCGplayer product", 280, "w", lambda r: r["tcg_name"].lower()),
    ("how", "Match", 95, "w", lambda r: r["match"]),
]
def help_text(s):
    n = lambda v: f"{v:g}"  # 5.0 -> "5"
    return (f"Status: URGENT = {n(s['urgent_pct'])}%+ away from TCGplayer · DRIFTING = {n(s['drift_pct'])}%+ away "
            f"(presale items: {n(s['presale_urgent_pct'])}% / {n(s['presale_drift_pct'])}%) · CHECK MATCH = please "
            "confirm the TCGplayer product is right. Change these numbers in Settings.\n"
            "Margin = profit as % of the price, using Shopify's cost per item. ⚠ = TCGplayer's price is below our cost.\n"
            "TCGplayer prices are a once-a-day snapshot. ★ = presale · ⚡ = fast-moving (presale or new set), check it live "
            "· ✎ = price typed in with 'Enter live price…'.\n"
            "Double-click a row to open it on TCGplayer. Right-click for more options.")


IS_MAC = sys.platform == "darwin"
UI_FONT = "Segoe UI" if sys.platform == "win32" else ("Helvetica Neue" if IS_MAC else "DejaVu Sans")
FS = 3 if IS_MAC else 0  # Mac points render smaller
MULTI_CLICK = "⌘-click" if IS_MAC else "Ctrl+click"


def font(size, *style):
    return (UI_FONT, size + FS, *style)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("TCG Price Checker")
        try:
            import base64
            self._icon = tk.PhotoImage(data=base64.b64encode(icon_png(64)))
            self.iconphoto(True, self._icon)
        except tk.TclError:
            pass
        self.geometry("1400x800")
        self.minsize(900, 500)
        self.checker = PriceChecker()
        self.events = queue.Queue()
        self.busy = False
        self.filter = tk.StringVar(value="All")
        self.search = tk.StringVar()
        self.sort_key, self.sort_reverse = None, False
        self.visible = []
        self._build_ui()
        self.after(100, self._poll)
        self.after(300, self.start_check)

    # ------------------------------------------------------------------ layout
    def _build_ui(self):
        style = ttk.Style(self)
        style.configure("Big.TButton", font=font(11, "bold"), padding=(14, 6))
        style.configure("Treeview", rowheight=24 + 2 * FS, font=font(10))
        style.configure("Treeview.Heading", font=font(10, "bold"))

        top = ttk.Frame(self, padding=(12, 10, 12, 4))
        top.pack(fill="x")
        ttk.Label(top, text="TCG Price Checker", font=font(16, "bold")).pack(side="left")
        self.run_btn = ttk.Button(top, text="▶  Check prices now", style="Big.TButton", command=self.start_check)
        self.run_btn.pack(side="left", padx=(20, 6))
        ttk.Button(top, text="Open printable report", command=self.open_report).pack(side="left", padx=4)
        ttk.Button(top, text="Saved choices", command=self.open_saved).pack(side="left", padx=4)
        ttk.Button(top, text="Settings", command=self.open_settings).pack(side="left", padx=4)
        self.progress = ttk.Progressbar(top, mode="indeterminate", length=160)
        self.progress.pack(side="right")
        self.status = ttk.Label(top, text="", foreground="#555")
        self.status.pack(side="right", padx=10)

        bar = ttk.Frame(self, padding=(12, 4))
        bar.pack(fill="x")
        self.filter_buttons = {}
        for label, _ in FILTERS:
            b = ttk.Radiobutton(bar, text=label, value=label, variable=self.filter, style="Toolbutton",
                                command=self.refresh_table)
            b.pack(side="left", padx=2)
            self.filter_buttons[label] = b
        ttk.Label(bar, text="Search:").pack(side="left", padx=(20, 4))
        entry = ttk.Entry(bar, textvariable=self.search, width=34)
        entry.pack(side="left")
        self.search.trace_add("write", lambda *_: self.refresh_table())

        body = ttk.Frame(self, padding=(12, 4))
        body.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(body, columns=[c[0] for c in COLUMNS], show="headings", selectmode="browse")
        for cid, heading, width, anchor, _ in COLUMNS:
            self.tree.heading(cid, text=heading, command=lambda c=cid: self.sort_by(c))
            self.tree.column(cid, width=width, minwidth=40, anchor=anchor, stretch=False)
        for tag, color in ROW_COLORS.items():
            self.tree.tag_configure(tag, background=color, foreground="#1d1d1b")
        ysb = ttk.Scrollbar(body, orient="vertical", command=self.tree.yview)
        xsb = ttk.Scrollbar(body, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)
        self.tree.bind("<Double-1>", lambda e: self.open_tcgplayer())
        for button in (("<Button-2>", "<Control-Button-1>") if IS_MAC else ("<Button-3>",)):
            self.tree.bind(button, self._context_menu)
        self.tree.bind("<<TreeviewSelect>>", lambda e: self._update_detail())

        actions = ttk.Frame(self, padding=(12, 4, 12, 2))
        actions.pack(fill="x")
        self.action_buttons = [
            ttk.Button(actions, text="Open on TCGplayer", command=self.open_tcgplayer),
            ttk.Button(actions, text="✓ Match is correct", command=self.confirm_match),
            ttk.Button(actions, text="Choose a different match…", command=self.change_match),
            ttk.Button(actions, text="Enter live price…", command=self.enter_live_price),
            ttk.Button(actions, text="We price this ourselves", command=self.toggle_self_priced),
            ttk.Button(actions, text="Hide this product", command=self.hide_product),
            ttk.Button(actions, text="Undo my choice", command=self.reset_choice),
        ]
        for b in self.action_buttons:
            b.pack(side="left", padx=(0, 6))
            b.state(["disabled"])
        self.detail = ttk.Label(self, text="", padding=(12, 2), foreground="#333", wraplength=1300, justify="left")
        self.detail.pack(fill="x")
        self.help = ttk.Label(self, text=help_text(self.checker.config["settings"]), padding=(12, 2, 12, 10),
                              foreground="#777", justify="left")
        self.help.pack(fill="x")

        self.menu = tk.Menu(self, tearoff=0)
        for b in self.action_buttons:
            self.menu.add_command(label=b.cget("text"), command=b.cget("command"))

    # ------------------------------------------------------------------ background work
    def run_in_background(self, label, work, done=None):
        if self.busy:
            return
        self.busy = True
        self.run_btn.state(["disabled"])
        self.progress.start(12)
        self.status.config(text=label)
        self.config(cursor="watch")

        def worker():
            try:
                result = work(lambda msg: self.events.put(("progress", msg)))
                self.events.put(("done", (done, result)))
            except SetupError as e:
                self.events.put(("error", str(e)))
            except Exception as e:  # network trouble etc. - show it, keep a log for whoever maintains this
                log = Path(HERE) / "error_log.txt"
                log.write_text(traceback.format_exc(), encoding="utf-8")
                self.events.put(("error", f"Something went wrong:\n\n{e}\n\nDetails were saved to {log}"))

        threading.Thread(target=worker, daemon=True).start()

    def _poll(self):
        try:
            while True:
                kind, payload = self.events.get_nowait()
                if kind == "progress":
                    self.status.config(text=payload)
                    continue
                self.busy = False
                self.run_btn.state(["!disabled"])
                self.progress.stop()
                self.config(cursor="")
                if kind == "error":
                    self.status.config(text="Stopped - see message")
                    messagebox.showerror("TCG Price Checker", payload, parent=self)
                else:
                    done, result = payload
                    if done:
                        done(result)
        except queue.Empty:
            pass
        self.after(100, self._poll)

    def choose_login_file(self, parent, intro=None):
        """File picker for config.yaml; keeps asking until the file is usable or the person cancels.
        Returns the chosen path (already checked) or None."""
        if intro:
            messagebox.showinfo("TCG Price Checker", intro, parent=parent)
        while True:
            current = self.checker.credentials_path
            path = filedialog.askopenfilename(
                parent=parent, title="Choose your Shopify login file (config.yaml)",
                initialdir=str(current.parent) if current and current.parent.is_dir() else str(Path.home()),
                filetypes=[("YAML", "*.yaml *.yml"), ("All files", "*.*")])
            if not path:
                return None
            problem = check_credentials_file(path)
            if not problem:
                return path
            if not messagebox.askretrycancel("Not a Shopify login file", problem, parent=parent):
                return None

    def use_login_file(self, path):
        self.checker.credentials_path = Path(path)
        self.checker.config["settings"]["credentials_file"] = str(path)
        self.checker.save()

    def start_check(self):
        if not os.environ.get("SHOPIFY_TOKEN") and check_credentials_file(self.checker.credentials_path):
            # first run on this computer (or the file moved): ask for the Shopify login file, then remember it
            path = self.choose_login_file(self, intro=(
                "Please choose your config.yaml file. It holds the Shopify login "
                "(the shopify: section with store_url and client_id / client_secret).\n\n"
                "It's remembered, and you can change it any time in Settings."))
            if not path:
                self.status.config(text="No login file chosen. Choose it in Settings, then press Check prices now.")
                return
            self.use_login_file(path)

        def work(progress):
            self.checker.run(progress)
            return self.checker.write_reports()

        def done(paths):
            self.refresh_table()
            self.show_status()

        self.run_in_background("Starting…", work, done)

    def show_status(self):
        when, hours = self.checker.snapshot_age()
        age = f"TCGplayer prices from {when} ({hours:.0f} hours old)" if when else "TCGplayer snapshot time unknown"
        self.status.config(text=f"Checked {len(self.checker.rows)} sealed listings · {age}",
                           foreground="#b45309" if hours and hours > 30 else "#555")

    # ------------------------------------------------------------------ table
    def _row_text(self, r):
        product = r["shopify_title"] + (f"  —  {r['variant']}" if r["variant"] else "")
        amt = "" if r["diff_amt"] is None else ("+" if r["diff_amt"] > 0 else "−") + money(abs(r["diff_amt"]))
        margin = lambda m: "" if m is None else f"{m:.0f}%"
        tcg_margin = margin(r["tcg_margin_pct"]) + ("  ⚠" if r["below_cost"] else "")
        flags = ("★" if r["presale"] else "") + ("⚡" if r["fast_moving"] else "") + ("✎" if r["live_entered"] else "")
        return (r["tag"], flags, product, money(r["our_price"]), money(r["cost"]),
                margin(r["margin_pct"]), money(r["tcg_price"]), tcg_margin, pct(r["diff_pct"]), amt,
                r["tcg_name"] or "—", r["match"])

    def _matches_filter(self, r, code):
        if code is None:
            return True
        if code in ("presale", "below_cost", "fast_moving"):
            return r[code]
        return r["tag"] == code

    def refresh_table(self, fallback_index=None):
        """Redraw the list. If the selected row is gone, select the row now at fallback_index."""
        rows = self.checker.rows
        lowest = self.checker.config["settings"].get("tcg_price_field") == "lowPrice"
        self.tree.heading("tcg", text="TCG lowest" if lowest else "TCG market")
        counts = {label: sum(self._matches_filter(r, code) for r in rows) for label, code in FILTERS}
        for label, b in self.filter_buttons.items():
            b.config(text=f"{label} ({counts[label]})" if rows else label)
        code = dict(FILTERS)[self.filter.get()]
        needle = self.search.get().strip().lower()
        visible = [r for r in rows if self._matches_filter(r, code)
                   and (not needle or needle in f"{r['shopify_title']} {r['variant']} {r['tcg_name']}".lower())]
        if self.sort_key:
            key = next(c[4] for c in COLUMNS if c[0] == self.sort_key)
            visible.sort(key=key, reverse=self.sort_reverse)
        selected = self._selected()
        self.tree.delete(*self.tree.get_children())
        self.visible = visible
        for i, r in enumerate(visible):
            self.tree.insert("", "end", iid=str(i), values=self._row_text(r), tags=(r["tag"],))
            if selected and (r["shopify_title"], r["variant"]) == (selected["shopify_title"], selected["variant"]):
                self.tree.selection_set(str(i))
                self.tree.see(str(i))
        if not self.tree.selection() and fallback_index is not None and visible:
            i = str(min(fallback_index, len(visible) - 1))
            self.tree.selection_set(i)
            self.tree.see(i)
        self._update_detail()

    def sort_by(self, cid):
        self.sort_reverse = (not self.sort_reverse if self.sort_key == cid
                             else cid in ("diff", "amt", "ours", "tcg", "cost"))
        self.sort_key = cid
        self.refresh_table()

    def _selected(self):
        sel = self.tree.selection()
        return self.visible[int(sel[0])] if sel and int(sel[0]) < len(self.visible) else None

    def _update_detail(self):
        r = self._selected()
        for b in self.action_buttons:
            b.state(["!disabled"] if r else ["disabled"])
        if not r:
            self.detail.config(text="")
            return
        parts = [f"{r['shopify_title']}{' — ' + r['variant'] if r['variant'] else ''}  ({r['channel']}, {r['type']})"]
        if r["tcg_name"]:
            parts.append(f"TCGplayer: {r['tcg_name']}  ·  set: {r['tcg_set']}  ·  match: {r['match']}")
            parts.append(f"Compared against: {r['source'] or 'no TCGplayer price'}"
                         + (f"  ·  cheapest listing at snapshot time {money(r['tcg_low'])}" if r["tcg_low"] is not None else ""))
        if r["live_entered"]:
            entered = parse_time(r["live_entered"]).astimezone().strftime("%b %d, %I:%M %p").replace(" 0", " ")
            parts.append(f"✎ TCGplayer price typed in {entered}: {money(r['tcg_price'])}  "
                         f"(daily snapshot: {money(r['snapshot_price']) or 'no price'})")
        elif r["tag"] == "NO PRICE":
            parts.append("TCGplayer has no listings for this today, so the daily snapshot has no Market Price for it. "
                         "Open it on TCGplayer and use 'Enter live price…' to type in the Market Price shown there. "
                         "It's kept until the snapshot has a price again.")
        elif r["fast_moving"]:
            parts.append("⚡ Fast-moving: the daily snapshot may be out of date. Use 'Enter live price…' to check it.")
        if r["cost"]:
            parts.append(f"Cost per item {money(r['cost'])}  ·  profit at our price {money(r['our_price'] - r['cost'])}"
                         + (f"  ·  profit at TCGplayer price {money(r['tcg_price'] - r['cost'])}" if r["tcg_price"] else "")
                         + ("  ·  ⚠ TCGplayer is below our cost" if r["below_cost"] else ""))
        else:
            parts.append("No cost per item in Shopify")
        if r["presale"] and r["release"]:
            parts.append(f"Presale · releases {r['release']}")
        if r["note"]:
            parts.append(r["note"])
        self.detail.config(text="\n".join(parts))

    def _context_menu(self, event):
        row = self.tree.identify_row(event.y)
        if row:
            self.tree.selection_set(row)
            self.menu.tk_popup(event.x_root, event.y_root)

    # ------------------------------------------------------------------ row actions
    def open_tcgplayer(self):
        r = self._selected()
        if r and r["tcg_urls"]:
            for url in r["tcg_urls"][:3]:
                webbrowser.open(url)
        elif r:
            self.change_match()

    def _save_choice(self, r, **fields):
        sel = self.tree.selection()
        set_override(self.checker.config, r["shopify_title"], r["variant"], **fields)
        self.checker.save()
        self.checker.recompute_title(r["shopify_title"])
        # if the row drops out of this list (e.g. confirmed in "Check match"), move on to the next one
        self.refresh_table(fallback_index=int(sel[0]) if sel else None)

    def confirm_match(self):
        r = self._selected()
        if not r:
            return
        if not r["tcg_refs"]:
            messagebox.showinfo("TCG Price Checker", "This product has no TCGplayer match yet.\n"
                                "Use 'Choose a different match…' to pick one.", parent=self)
            return
        self._save_choice(r, tcg=r["tcg_refs"])

    def change_match(self):
        r = self._selected()
        if r:
            MatchPicker(self, r)

    def enter_live_price(self):
        """Type in the price TCGplayer shows right now; it's used until tcgcsv's next daily snapshot."""
        r = self._selected()
        if not r:
            return
        if not r["tcg_refs"]:
            messagebox.showinfo("Enter live price", "Choose the TCGplayer match first.", parent=self)
            return
        for url in r["tcg_urls"][:1]:
            webbrowser.open(url)
        current = f"{r['tcg_price']:.2f}" if r["tcg_price"] else ""
        text = simpledialog.askstring(
            "Enter live price",
            f"{r['shopify_title']}{' — ' + r['variant'] if r['variant'] else ''}\n\n"
            f"Today's snapshot price: {money(r['snapshot_price']) or 'none'}\n"
            "TCGplayer is opening in your browser.\n"
            + ("Type the 'As low as' price at the top of the page (the cheapest listing).\n"
               if self.checker.config["settings"].get("tcg_price_field") == "lowPrice" else
               "Scroll down to 'Price Points' and type the Market Price.\n"
               "(Not the big price at the top: that's just the cheapest listing.)\n")
            + "It's used until the next daily snapshot. Leave empty to go back to the snapshot.",
            initialvalue=current, parent=self)
        if text is None:
            return
        text = text.strip().replace("$", "").replace(",", "")
        try:
            price = float(text) if text else None
        except ValueError:
            messagebox.showerror("Enter live price", f"'{text}' isn't a price.", parent=self)
            return
        set_live_price(self.checker.config, r["shopify_title"], r["variant"], price)
        self.checker.save()
        sel = self.tree.selection()
        self.checker.recompute_title(r["shopify_title"])
        self.refresh_table(fallback_index=int(sel[0]) if sel else None)

    def toggle_self_priced(self):
        r = self._selected()
        if not r:
            return
        current = find_override(self.checker.config, r["shopify_title"], r["variant"]) or {}
        fields = {k: v for k, v in current.items() if k not in ("shopify_title", "variant")}
        if r["tag"] == "SELF-PRICED" and current.get("self_priced"):
            fields.pop("self_priced", None)
        else:
            fields["self_priced"] = True
            fields.setdefault("tcg", r["tcg_refs"])
        self._save_choice(r, **fields)

    def hide_product(self):
        r = self._selected()
        if r and messagebox.askyesno("Hide product", f"Stop checking this product?\n\n{r['shopify_title']}"
                                     "\n\nYou can bring it back from 'Saved choices'.", parent=self):
            self._save_choice(r, ignore=True)

    def reset_choice(self):
        r = self._selected()
        if r:
            self._save_choice(r)

    # ------------------------------------------------------------------ windows
    def open_report(self):
        if not self.checker.rows:
            messagebox.showinfo("TCG Price Checker", "Run a price check first.", parent=self)
            return
        html_path, _ = self.checker.write_reports()
        webbrowser.open(html_path.as_uri())

    def open_saved(self):
        SavedChoices(self)

    def open_settings(self):
        Settings(self)


class MatchPicker(tk.Toplevel):
    """Search TCGplayer sealed products and pick the right one (or several to average)."""

    def __init__(self, app, row):
        super().__init__(app)
        self.app, self.row = app, row
        self.title("Choose the TCGplayer product")
        self.geometry("1000x560")
        self.transient(app)
        ttk.Label(self, text=row["shopify_title"] + (f" — {row['variant']}" if row["variant"] else ""),
                  font=font(11, "bold"), padding=(12, 10, 12, 2)).pack(fill="x")
        ttk.Label(self, text=f"Pick the matching TCGplayer product. Select several ({MULTI_CLICK}) to use their "
                  "average price.", padding=(12, 0, 12, 6), foreground="#555").pack(fill="x")
        bar = ttk.Frame(self, padding=(12, 0))
        bar.pack(fill="x")
        self.query = tk.StringVar(value=SHOPIFY_NOISE.sub(" ", f"{row['shopify_title']} {row['variant']}").strip())
        entry = ttk.Entry(bar, textvariable=self.query)
        entry.pack(side="left", fill="x", expand=True)
        entry.bind("<Return>", lambda e: self.search())
        ttk.Button(bar, text="Search", command=self.search).pack(side="left", padx=6)

        frame = ttk.Frame(self, padding=(12, 6))
        frame.pack(fill="both", expand=True)
        cols = [("name", "TCGplayer product", 420), ("set", "Set", 240), ("game", "Game", 150),
                ("price", "Price", 80), ("score", "Fit", 50)]
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in cols], show="headings", selectmode="extended")
        for cid, text, width in cols:
            self.tree.heading(cid, text=text)
            self.tree.column(cid, width=width, anchor="e" if cid in ("price", "score") else "w")
        ysb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ysb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        ysb.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", lambda e: self.use())

        buttons = ttk.Frame(self, padding=(12, 4, 12, 12))
        buttons.pack(fill="x")
        ttk.Button(buttons, text="Use selected", style="Big.TButton", command=self.use).pack(side="left")
        ttk.Button(buttons, text="Open selected on TCGplayer", command=self.open_selected).pack(side="left", padx=6)
        ttk.Button(buttons, text="Not on TCGplayer - we price it ourselves", command=self.self_priced).pack(side="left", padx=6)
        ttk.Button(buttons, text="Cancel", command=self.destroy).pack(side="right")
        self.results = []
        self.search()

    def search(self):
        self.config(cursor="watch")
        self.update_idletasks()
        try:
            self.results = self.app.checker.search_tcg(self.query.get())
        finally:
            self.config(cursor="")
        self.tree.delete(*self.tree.get_children())
        current = {(t["category"], t["group"], t["product"]) for t in self.row["tcg_refs"]}
        for i, (score, p, price) in enumerate(self.results):
            self.tree.insert("", "end", iid=str(i), values=(p["name"], p["set"], p["game"], money(price), f"{score:.0%}"))
            if (p["category"], p["group"], p["id"]) in current:
                self.tree.selection_add(str(i))

    def _picked(self):
        return [self.results[int(i)][1] for i in self.tree.selection()]

    def use(self):
        picked = self._picked()
        if not picked:
            messagebox.showinfo("Choose", "Select at least one product.", parent=self)
            return
        self.app._save_choice(self.row, tcg=[{"category": p["category"], "group": p["group"], "product": p["id"]}
                                             for p in picked])
        self.destroy()

    def self_priced(self):
        self.app._save_choice(self.row, self_priced=True)
        self.destroy()

    def open_selected(self):
        for p in self._picked()[:3]:
            if p.get("url"):
                webbrowser.open(p["url"])


class SavedChoices(tk.Toplevel):
    """Every match/choice someone has saved, with a way to undo it."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Saved choices")
        self.geometry("1000x500")
        self.transient(app)
        ttk.Label(self, text="Choices saved by people. These always win over automatic matching.",
                  padding=(12, 10, 12, 6)).pack(fill="x")
        frame = ttk.Frame(self, padding=(12, 0))
        frame.pack(fill="both", expand=True)
        cols = [("product", "Shopify product", 480), ("choice", "Choice", 420)]
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in cols], show="headings")
        for cid, text, width in cols:
            self.tree.heading(cid, text=text)
            self.tree.column(cid, width=width)
        ysb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ysb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        ysb.pack(side="right", fill="y")
        buttons = ttk.Frame(self, padding=12)
        buttons.pack(fill="x")
        ttk.Button(buttons, text="Remove selected choice", command=self.remove).pack(side="left")
        ttk.Button(buttons, text="Close", command=self.destroy).pack(side="right")
        self.fill()

    def describe(self, o):
        if o.get("ignore"):
            return "Hidden from the check"
        names = []
        for t in o.get("tcg", []):
            p = self.app.checker.index.product(t["category"], t["group"], t["product"])
            names.append(p["name"] if p else f"TCGplayer #{t['product']}")
        text = " + ".join(names) if names else ""
        if len(names) > 1:
            text = "Average of: " + text
        if o.get("self_priced"):
            text = "We price this ourselves" + (f" (reference: {text})" if text else "")
        return text

    def fill(self):
        self.tree.delete(*self.tree.get_children())
        for i, o in enumerate(self.app.checker.config["overrides"]):
            product = o["shopify_title"] + (f" — {o['variant']}" if o.get("variant") else "")
            self.tree.insert("", "end", iid=str(i), values=(product, self.describe(o)))

    def remove(self):
        sel = self.tree.selection()
        if not sel:
            return
        o = self.app.checker.config["overrides"][int(sel[0])]
        set_override(self.app.checker.config, o["shopify_title"], o.get("variant", ""))
        self.app.checker.save()
        if self.app.checker.shopify_items:
            self.app.checker.recompute_title(o["shopify_title"])
            self.app.refresh_table()
        self.fill()


class Settings(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Settings")
        self.transient(app)
        self.resizable(False, False)
        s = app.checker.config["settings"]
        f = ttk.Frame(self, padding=16)
        f.pack(fill="both", expand=True)
        self.vars = {}
        r = 0
        for key, label in [("drift_pct", "Drifting when our price is at least this % away"),
                           ("urgent_pct", "Urgent when our price is at least this % away"),
                           ("presale_drift_pct", "Presale: drifting at %"),
                           ("presale_urgent_pct", "Presale: urgent at %")]:
            ttk.Label(f, text=label).grid(row=r, column=0, sticky="w", pady=3)
            v = tk.StringVar(value=str(s[key]))
            ttk.Spinbox(f, from_=0, to=100, increment=1, textvariable=v, width=6).grid(row=r, column=1, sticky="w")
            self.vars[key] = v
            r += 1

        ttk.Label(f, text="Compare our price against TCGplayer's").grid(row=r, column=0, sticky="w", pady=3)
        self.field = tk.StringVar(value=s.get("tcg_price_field", "marketPrice"))
        fr = ttk.Frame(f)
        fr.grid(row=r, column=1, columnspan=2, sticky="w")
        ttk.Radiobutton(fr, text="Market price", value="marketPrice", variable=self.field).pack(side="left")
        ttk.Radiobutton(fr, text="Lowest listing", value="lowPrice", variable=self.field).pack(side="left", padx=10)
        r += 1
        ttk.Label(f, text="Flag as fast-moving when the set came out within this many days").grid(row=r, column=0, sticky="w", pady=3)
        self.vars["new_release_days"] = tk.StringVar(value=str(s.get("new_release_days", 30)))
        ttk.Spinbox(f, from_=0, to=365, increment=1, textvariable=self.vars["new_release_days"], width=6).grid(row=r, column=1, sticky="w")
        r += 1

        ttk.Separator(f).grid(row=r, column=0, columnspan=3, sticky="ew", pady=10)
        r += 1
        ttk.Label(f, text="Shopify product types to check (singles are never checked):").grid(row=r, column=0, columnspan=3, sticky="w")
        r += 1
        types_frame = ttk.Frame(f)
        types_frame.grid(row=r, column=0, columnspan=3, sticky="w")
        known = app.checker.product_types() or [(t, None) for t in s["sealed_types"]]
        chosen = {t.lower() for t in s["sealed_types"]}
        self.type_vars = {}
        for i, (t, n) in enumerate(t for t in known if t[0] and t[0].lower() != "singles"):
            v = tk.BooleanVar(value=t.lower() in chosen)
            ttk.Checkbutton(types_frame, text=f"{t} ({n})" if n else t, variable=v).grid(row=i // 4, column=i % 4, sticky="w", padx=(0, 12))
            self.type_vars[t] = v
        r += 1
        self.drafts = tk.BooleanVar(value=s.get("include_drafts", False))
        ttk.Checkbutton(f, text="Also check draft (not published) products", variable=self.drafts).grid(row=r, column=0, columnspan=3, sticky="w", pady=(6, 0))
        r += 1

        ttk.Separator(f).grid(row=r, column=0, columnspan=3, sticky="ew", pady=10)
        r += 1
        for key, label in [("ignore_words", "Skip products whose title contains (comma separated):"),
                           ("self_priced_words", "We price it ourselves when the title contains:")]:
            ttk.Label(f, text=label).grid(row=r, column=0, columnspan=3, sticky="w")
            v = tk.StringVar(value=", ".join(w.strip() for w in s[key]))
            ttk.Entry(f, textvariable=v, width=80).grid(row=r + 1, column=0, columnspan=3, sticky="we", pady=(0, 6))
            self.vars[key] = v
            r += 2

        ttk.Label(f, text="Shopify login file (config.yaml):").grid(row=r, column=0, columnspan=3, sticky="w")
        self.cred = tk.StringVar(value=str(app.checker.credentials_path or "(not chosen yet)"))
        ttk.Entry(f, textvariable=self.cred, width=70, state="readonly").grid(row=r + 1, column=0, columnspan=2, sticky="we")
        ttk.Button(f, text="Choose file…", command=self.browse).grid(row=r + 1, column=2, padx=6)
        r += 2

        buttons = ttk.Frame(f)
        buttons.grid(row=r, column=0, columnspan=3, sticky="e", pady=(14, 0))
        ttk.Button(buttons, text="Save", command=self.save).pack(side="left", padx=6)
        ttk.Button(buttons, text="Cancel", command=self.destroy).pack(side="left")

    def browse(self):
        path = self.app.choose_login_file(self)
        if path:
            self.cred.set(path)

    def save(self):
        s = self.app.checker.config["settings"]
        try:
            for key in ("drift_pct", "urgent_pct", "presale_drift_pct", "presale_urgent_pct"):
                s[key] = float(self.vars[key].get())
            s["new_release_days"] = int(float(self.vars["new_release_days"].get()))
        except ValueError:
            messagebox.showerror("Settings", "The percentages must be numbers.", parent=self)
            return
        s["tcg_price_field"] = self.field.get()
        s["sealed_types"] = [t for t, v in self.type_vars.items() if v.get()]
        s["include_drafts"] = self.drafts.get()
        for key in ("ignore_words", "self_priced_words"):
            s[key] = [w.strip() for w in self.vars[key].get().split(",") if w.strip()]
        if not check_credentials_file(self.cred.get()):
            self.app.checker.credentials_path = Path(self.cred.get())
            s["credentials_file"] = self.cred.get()
        self.app.checker.save()
        self.app.help.config(text=help_text(s))
        self.destroy()
        if self.app.checker.shopify_items:
            self.app.run_in_background("Applying settings…", lambda progress: self.app.checker.recompute(progress),
                                       lambda _: self.app.refresh_table())


# ================================================================ entry point

def cli_main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cli", action="store_true", help="run once in the console instead of opening the window")
    ap.add_argument("--config", default=HERE / "products.json", type=Path)
    ap.add_argument("--credentials", type=Path,
                    help="config.yaml with a shopify: section (default: the file chosen in the window)")
    ap.add_argument("--shopify-csv", type=Path, help="Shopify product export instead of the API")
    ap.add_argument("--out", default=HERE / "reports", type=Path)
    args = ap.parse_args(argv)
    if sys.stdout:  # (a packaged windowed app has no console)
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # Windows consoles default to cp1252

    checker = PriceChecker(args.config, args.credentials, args.out)
    try:
        rows = checker.run(progress=print, shopify_csv=args.shopify_csv)
    except SetupError as e:
        sys.exit(str(e))
    checker.save()
    html_path, csv_path = checker.write_reports()
    counts = {t: sum(r["tag"] == t for r in rows) for t in TAG_ORDER}
    print("\n" + " · ".join(f"{t.title()}: {n}" for t, n in counts.items() if n))
    print(f"Report: {html_path}\nCSV:    {csv_path}")


# ================================================================ app icon (drawn in code: no image files needed)

def icon_png(size=64):
    """PNG bytes of the app icon: two trading cards, the front one with a little price chart."""
    import struct
    import zlib

    def rounded(x, y, x0, y0, x1, y1, r):
        cx = min(max(x, x0 + r), x1 - r)
        cy = min(max(y, y0 + r), y1 - r)
        return x0 <= x <= x1 and y0 <= y <= y1 and (x - cx) ** 2 + (y - cy) ** 2 <= r * r

    rows = []
    for py_ in range(size):
        row = bytearray([0])  # PNG filter byte
        for px in range(size):
            x, y = px / size, py_ / size
            color = (0, 0, 0, 0)
            if rounded(x, y, 0.10, 0.06, 0.62, 0.78, 0.07):                       # back card
                color = (245, 158, 11, 255)
            if rounded(x, y, 0.32, 0.20, 0.90, 0.95, 0.07):                       # front card
                color = (30, 79, 184, 255)
                if rounded(x, y, 0.37, 0.25, 0.85, 0.90, 0.05):
                    color = (255, 255, 255, 255)
                    for bx, top, fill in ((0.43, 0.62, (220, 38, 38)), (0.56, 0.48, (245, 158, 11)),
                                          (0.69, 0.36, (22, 163, 74))):           # chart bars
                        if bx <= x <= bx + 0.09 and top <= y <= 0.82:
                            color = (*fill, 255)
            row += bytes(color)
        rows.append(bytes(row))

    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)

    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(b"".join(rows), 9)) + chunk(b"IEND", b""))


def write_icon(path):
    """Save the icon for building the app: .ico (Windows) or .png (Mac, PyInstaller converts it)."""
    import struct
    path = Path(path)
    if path.suffix.lower() != ".ico":
        path.write_bytes(icon_png(512))
        return
    images = [(s, icon_png(s)) for s in (16, 32, 48, 256)]
    offset = 6 + 16 * len(images)
    header = struct.pack("<HHH", 0, 1, len(images))
    for s, png in images:
        header += struct.pack("<BBBBHHII", s % 256, s % 256, 0, 0, 1, 32, len(png), offset)
        offset += len(png)
    path.write_bytes(header + b"".join(png for _, png in images))


def build_app():
    """Package this script as a stand-alone app for the computer it's run on (Python not needed afterwards).

    Windows -> "TCG Price Checker.exe", Mac -> "TCG Price Checker.app", both placed next to this script.
    Uses a throwaway build folder with PyInstaller, so nothing is installed into your own Python.
    """
    import shutil
    import subprocess
    import tempfile
    import venv

    name = "TCG Price Checker"
    script = Path(__file__).resolve()
    work = Path(tempfile.mkdtemp(prefix="tcg_build_"))
    print(f"Building {name} in {work} ... (takes a few minutes the first time)")
    venv.create(work / "venv", with_pip=True)
    py = work / "venv" / ("Scripts/python.exe" if sys.platform == "win32" else "bin/python")
    subprocess.run([str(py), "-m", "pip", "install", "--quiet", "pyinstaller", "pillow"], check=True)
    icon = work / ("icon.ico" if sys.platform == "win32" else "icon.png")
    write_icon(icon)
    args = [str(py), "-m", "PyInstaller", "--noconfirm", "--windowed", "--name", name, "--icon", str(icon),
            "--distpath", str(work / "dist"), "--workpath", str(work / "build"), "--specpath", str(work)]
    if sys.platform == "darwin":
        args += ["--osx-bundle-identifier", "com.tcgpricechecker.app"]
    else:
        args += ["--onefile"]
    subprocess.run(args + [str(script)], check=True)
    built = work / "dist" / (f"{name}.app" if sys.platform == "darwin" else f"{name}.exe")
    target = script.parent / built.name
    if target.is_dir():
        shutil.rmtree(target)
    elif target.exists():
        target.unlink()
    shutil.move(str(built), str(target))
    shutil.rmtree(work, ignore_errors=True)
    print(f"\nDone: {target}\nMove it anywhere. Its saved choices, cache and reports stay in the folder next to it.")


def hide_own_console():
    """On Windows, double-clicking a .py file opens a black console window next to ours: hide it.
    Leaves the console alone when it belongs to a terminal someone typed the command into."""
    if sys.platform != "win32":
        return
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        if kernel32.GetConsoleProcessList((ctypes.c_uint * 2)(), 2) == 1:  # only us in this console
            ctypes.windll.user32.ShowWindow(kernel32.GetConsoleWindow(), 0)
    except Exception:
        pass


if __name__ == "__main__":
    if sys.argv[1:2] == ["--write-icon"]:  # used when building the app
        write_icon(sys.argv[2])
    elif "--build-app" in sys.argv[1:]:
        build_app()
    elif "--cli" in sys.argv[1:]:
        cli_main(sys.argv[1:])
    else:
        hide_own_console()
        App().mainloop()
