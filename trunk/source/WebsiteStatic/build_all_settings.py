#!/usr/bin/python3

import os
from build_settings import compute_settings

SCRIPT_DIR  = os.path.dirname(__file__)
EPF_ROOT    = os.path.join(SCRIPT_DIR, '../../examples/settings/')
WORKER_ROOT = os.path.join(SCRIPT_DIR, 'webinterface/workers/')


WORKER_SETTINGS = {
    "boogieAutomizer":      "default/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
    "cAutomizer":           "default/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
    "boogieBuchiAutomizer": "default/automizer/svcomp-Termination-32bit-Automizer_Default.epf",
    "cBuchiAutomizer":      "default/automizer/svcomp-Termination-32bit-Automizer_Default.epf",
    "boogieGemCutter":      "default/gemcutter/svcomp-Reach-32bit-GemCutter_Default.epf",
    "cGemCutter":           "default/gemcutter/svcomp-Reach-32bit-GemCutter_Default.epf",
    "boogieKojak":          "default/kojak/svcomp-Reach-32bit-Kojak_Default.epf",
    "cKojak":               "default/kojak/svcomp-Reach-32bit-Kojak_Default.epf",
    "boogieTaipan":         "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
    "cTaipan":              "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
    "cLTLAutomizer":        "default/automizer/svcomp-LTL-32bit-Automizer_Default.epf",
    "boogieLassoRanker":    "webinterface/LassoRanker.epf",
    "cLassoRanker":         "webinterface/LassoRanker.epf",
    "automataScript":       "AutomataScript/default.epf",
    "boogieReferee":        "webinterface/Referee.epf",
    "cReferee":             "webinterface/Referee.epf",
    "smtEliminator":        "webinterface/Eliminator.epf",
}

def build_settings(worker):
    print(f"Generating {worker} settings...")

    overrides = get_override_path(worker)
    toolchain = os.path.join(WORKER_ROOT, worker + '.xml')
    settings  = os.path.join(EPF_ROOT, WORKER_SETTINGS[worker])

    json = compute_settings(toolchain, settings, overrides)

    # write settings JSON to suitable file
    output_path = os.path.join(WORKER_ROOT, worker + '.json')
    with open(output_path, 'w') as file:
        file.write(json)


def get_override_path(worker):
    path = os.path.join(WORKER_ROOT, worker + '.override.json')
    if os.path.isfile(path):
        return path
    return None

def main():
    for worker in WORKER_SETTINGS:
        build_settings(worker)

if __name__ == "__main__":
    main()

