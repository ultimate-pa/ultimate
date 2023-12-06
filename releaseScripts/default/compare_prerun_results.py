#!/usr/local/bin/python3

###############################################################################
# Collects prerun results from different tools and creates a comparison table.
###############################################################################
# Installation instructions:
#
# To get requests_html working, I executed the following commands:
# (Warning: This installs Google Chrome.)
#
# $> pip3 install requests_html
# $> wget -q -O - https://dl-ssl.google.com/linux/linux_signing_key.pub | apt-key add -
# $> echo 'deb [arch=amd64] http://dl.google.com/linux/chrome/deb/ stable main' | tee /etc/apt/sources.list.d/google-chrome.list
# $> apt-get update
# $> apt-get install -y google-chrome-stable
#
from requests_html import HTMLSession
#
###############################################################################
# Configuration:
#
root_url = "https://sv-comp.sosy-lab.org/2024/results/results-verified"
categories = [
  "unreach-call.ConcurrencySafety-Main",
  "no-data-race.NoDataRace-Main",
  "no-overflow.ConcurrencySafety-NoOverflows",
  "valid-memsafety.ConcurrencySafety-MemSafety",
]
data_layout = {
  'raw_score'                 : { 'row': 'all results',                 'column': 3 },
  'correct_confirmed'         : { 'row': 'correct results',             'column': 2 },
  'correct_true_confirmed'    : { 'row': 'correct true',                'column': 2 },
  'correct_false_confirmed'   : { 'row': 'correct false',               'column': 2 },
  'correct_unconfirmed'       : { 'row': 'correct-unconfirmed results', 'column': 2, 'optional': True },
  'correct_true_unconfirmed'  : { 'row': 'correct-unconfirmed results', 'column': 2, 'optional': True },
  'correct_false_unconfirmed' : { 'row': 'correct-unconfirmed results', 'column': 2, 'optional': True },
  'incorrect'                 : { 'row': 'incorrect results',           'column': 2 },
  'incorrect_true'            : { 'row': 'incorrect true',              'column': 2 },
  'incorrect_false'           : { 'row': 'incorrect false',             'column': 2 },
}
#
###############################################################################

def find_pages(html, category):
  pages = {}
  links = html.find("a")
  for link in links:
    url = link.attrs['href']
    if category in url:
      (tool, _) = url.split('.', 1)
      (pruned_url, _) = url.split('#', -1)
      pages[tool] = pruned_url
  return pages

def get_title(row):
  return row.find("div.td[role='cell'] div.row-title")[0].text

def find_row(rows, title):
  for row in rows:
    if get_title(row) == title:
      return row
  return None

def extract_data(rows):
  global data_layout

  data = {}
  for key, info in data_layout.items():
    row = find_row(rows, info["row"])
    if row is not None:
      data[key] = int(row.find("div.td[role='cell']")[info['column']].text)
    elif not info.get("optional", False):
      print(f"    missing row: {info['row']}")
      return None

  return data

def print_table(category, results):
  print(category)
  print("--------------------------------------------------------------------------------")

  print()
  print("| tool            || score   | correct (conf.) | correct true   | correct false   || incorrect | incorrect true | incorrect false |")
  print("|-----------------||---------|-----------------|----------------|-----------------||-----------|----------------|-----------------|")
  for tool, data in sorted(results.items(), key=lambda pair: int(pair[1]['raw_score']), reverse=True):
    print(f"| {tool:<15} ||   {data['raw_score']:5} |       {data['correct_confirmed']+data.get('correct_unconfirmed',0):3} ({data['correct_confirmed']:3}) |      {data['correct_true_confirmed']+data.get('correct_true_unconfirmed',0):3} ({data['correct_true_confirmed']:3}) |       {data['correct_false_confirmed']+data.get('correct_falseunconfirmed',0):3} ({data['correct_false_confirmed']:3}) ||       {data['incorrect']:3} |            {data['incorrect_true']:3} |             {data['incorrect_false']:3} |")
  print()

  print()
  print()

###############################################################################

print()
overview = HTMLSession().get(f"{root_url}/results-per-tool.php")
results={}

for category in categories:
  print(f"Loading data for category {category}...")
  results[category] = {}
  pages = find_pages(overview.html, category)

  for tool, url in pages.items():
    print("  loading data for " + tool + "...")
    tooldata = HTMLSession().get(f"{root_url}/{url}")
    tooldata.html.render(retries=3, wait=3, timeout=16)

    rows = tooldata.html.find("div.table-body div.tr[role='row']")
    data = extract_data(rows)
    if data is None:
      print(f"    No (or incomplete) data found for {tool}; skipping.")
      continue

    results[category][tool] = data

  print()

print()
print()

for category, data in results.items():
  print_table(category, data)
