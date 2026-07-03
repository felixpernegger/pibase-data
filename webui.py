#!/usr/bin/env python3
"""Local web UI for the pi-base implications tool.

  ./webui.py [--port 8765] [--no-browser]

Serves a single page on http://localhost:PORT with the same triage workflow
as the interactive terminal tool: draw a random unknown implication, assert
it true/false with an optional note (saved to assertions.json, with all the
same consistency guard rails), and browse/remove saved assertions. Property
names link to the pi-base website.
"""

import argparse
import io
import json
import random
import threading
import webbrowser
from contextlib import redirect_stdout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import deduce
import implications
from implications import CommandError, Engine

ROOT = Path(__file__).resolve().parent
PAGE = ROOT / "webui.html"


class State:
    def __init__(self):
        self.lock = threading.Lock()
        self.data = implications.load_data()
        self.engine = Engine(implications.load_assertions(), self.data)
        self._base_unknown = None  # unknown count without assertions, cached

    def rebuild(self):
        self.engine = Engine(implications.load_assertions(), self.data)
        counts, unknown = self.engine.classify()
        deduce.write_unknown_csv(ROOT / "unknown_pairs.csv",
                                 self.engine.prover, self.engine.props, unknown)
        return counts

    def base_unknown(self):
        if self._base_unknown is None:
            _, _, spaces = self.data
            base_with = deduce.literal_bitsets(
                self.engine.base_prover,
                list(deduce.close_spaces(self.engine.base_prover,
                                         spaces).values()))
            base_counts, _ = deduce.classify_pairs(self.engine.base_prover,
                                                   base_with)
            self._base_unknown = base_counts["unknown"]
        return self._base_unknown

    def lit_json(self, uid, value):
        return {"uid": uid, "value": value, "name": self.engine.props[uid]}

    def state_json(self):
        counts, _ = self.engine.classify()
        assertions = [
            {"index": i,
             "if": self.lit_json(a["if"]["property"], a["if"]["value"]),
             "then": self.lit_json(a["then"]["property"], a["then"]["value"]),
             "holds": a["holds"], "note": a.get("note", ""), "date": a["date"]}
            for i, a in enumerate(self.engine.assertions)]
        return {"counts": counts,
                "settled": self.base_unknown() - counts["unknown"],
                "spaces": len(self.engine.space_vals),
                "virtual": len(self.engine.virtual_vals),
                "assertions": assertions,
                "problems": self.engine.problems}

    def random_json(self):
        _, unknown = self.engine.classify()
        if not unknown:
            return {"done": True}
        a, b = random.choice(unknown)
        ua, va = self.engine.prover.unlit(a)
        ub, vb = self.engine.prover.unlit(b)
        return {"if": self.lit_json(ua, va), "then": self.lit_json(ub, vb)}

    def assert_json(self, body):
        stmt = ((body["if"]["uid"], bool(body["if"]["value"])),
                (body["then"]["uid"], bool(body["then"]["value"])))
        verdict = "true" if body["holds"] else "false"
        log = io.StringIO()
        with redirect_stdout(log):
            implications.do_assert(self.engine,
                                   implications.short_statement(stmt),
                                   verdict, body.get("note", ""))
            counts = self.rebuild()
            print(f"open list refreshed: {counts['unknown']} unknown, "
                  f"wrote unknown_pairs.csv")
        return {"log": log.getvalue(), "state": self.state_json()}

    def remove_json(self, body):
        log = io.StringIO()
        with redirect_stdout(log):
            implications.do_remove(self.engine, int(body["index"]))
            counts = self.rebuild()
            print(f"open list refreshed: {counts['unknown']} unknown, "
                  f"wrote unknown_pairs.csv")
        return {"log": log.getvalue(), "state": self.state_json()}


STATE = None  # set in main()


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):  # quiet
        pass

    def send_json(self, obj, code=200):
        payload = json.dumps(obj).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            payload = PAGE.read_bytes()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
        elif self.path == "/api/state":
            with STATE.lock:
                self.send_json(STATE.state_json())
        elif self.path == "/api/random":
            with STATE.lock:
                self.send_json(STATE.random_json())
        else:
            self.send_json({"error": "not found"}, 404)

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError:
            self.send_json({"error": "bad JSON"}, 400)
            return
        try:
            with STATE.lock:
                if self.path == "/api/assert":
                    self.send_json(STATE.assert_json(body))
                elif self.path == "/api/remove":
                    self.send_json(STATE.remove_json(body))
                else:
                    self.send_json({"error": "not found"}, 404)
        except CommandError as e:
            self.send_json({"error": str(e)}, 400)
        except (KeyError, TypeError, ValueError) as e:
            self.send_json({"error": f"bad request: {e}"}, 400)


def main():
    global STATE
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--port", type=int, default=8765)
    p.add_argument("--no-browser", action="store_true",
                   help="do not open the browser automatically")
    args = p.parse_args()

    print("loading pi-base data ...")
    STATE = State()
    for problem in STATE.engine.problems:
        print(f"warning: {problem}")

    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    url = f"http://localhost:{args.port}/"
    print(f"pi-base implications web UI: {url}  (Ctrl-C to stop)")
    if not args.no_browser:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nbye")


if __name__ == "__main__":
    main()
