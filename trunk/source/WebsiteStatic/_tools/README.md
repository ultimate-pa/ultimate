# ULTIMATE Tool Descriptions

This directory collects the detailed descriptions of the various ULTIMATE tools.

For each tool, there is a separate file.
It begins with metadata about the tool, described in the YAML format, between two lines of three dashes.
After the second line of dashes starts the HTML body content of the tool description page.

The metadata is used to describe the tool in the list of all tools on the main page (`../index.html`),
and to set up the web interface for the tool.


## Tool Web Interface
For the web interface, the `tool_id` key and the `worker` entries in the `languages` array are of particular importance.
For each worker, a correspondingly-named toolchain XML must exist in `../webinterface/workers`,
and a settings file to be used must be specified in `../build_all_settings.py`.

The script `../build_all_settings.py` then generates a JSON file with settings for the worker in `../webinterface/workers`.
Settings that should be visible in the web interface must be entered in a file `../webinterface/workers/<worker>.override.json`.

