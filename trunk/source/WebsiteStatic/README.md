# WebsiteStatic
This is the **Ultimate** framework website. It provides a front-end for the Ultimate framework web API implemented by ``WebBackend``.
It needs access to a running ``WebBackend`` applications API to run Ultimate jobs.

## Glossary
* **Tool**: An Ultimate tool, for example "Ultimate Automizer".
  * Defined in [config.js](config/config.js) under the key `tools`.
  * Assigned to a unique `tool.id`.
* **Worker**: Here a selected tool and a selected language. In Ultimate also called a toolchain.
  * Each tool can have multiple workers. A worker is a dictionary in a list of `workers` in a `tools` entry in [config.js](config/config.js)
  * Each worker of the website needs a unique id `id`.
  * Each worker needs a toolchain XML in [ultimate_toolchain_xmls](config/ultimate_toolchain_xmls) named `<id>.xml`

## Configuration and Setup
All configuration is set in `config/config.js`.
* Copy [config/config.dist.js](config/config.dist.js) to `config/config.js`.
* Edit `config/config.js` to your needs. The `config/config.dist.js` file is commented to guide the configuration.

You can generate the `frontend_settings` part of the configuration file for some settings using the Ultimate command line.

Example:

``` bash
./Ultimate -tc config/AutomizerReach.xml -s config/svcomp-Overflow-64bit-Automizer_Default.epf -i dummy --generate-frontend-json-from-delta
...
{"frontend_settings":[...]}
```

### Toolchain configuration
For each worker in `config.tools.worker` a toolchain named `<worker.id>.xml` must be available in
`config/ultimate_toolchain_xmls`. This toolchain XML can be edited to alter the toolchain.

### Code examples
All code examples for a specific worker are stored in `config/code_examples/<worker.id>`.

To **add or alter examples**:
1. Copy or edit one example in `config/code_examples/<worker.id>/<example_name>`.
2. Go to `config/code_examples` and run `refresh_index.py`

To recreate the initial examples available, go to `config/code_examples` and run `copy_initial_examples.py` and then
 `refresh_index.py`.

### Tool details page
Each tool is associated with a details page. To alter its content, edit the page matching the `tool_id` in the [config/tool_pages](config/tool_pages) folder.

### Homepage contents
The content sections are determined by the files in [config/home_page](config/home_page).

## Development

### Setup development environment
* Download a node package manager (for Windows, use <https://github.com/coreybutler/nvm-windows/releases>)
* Run `npm install` in `bootstrap_dev/`

### Expected result response example

```json
"results": [
    {
      "endCol": -1,
      "endLNr": -1,
      "logLvl": "warning",
      "longDesc": "unknown boogie variable #StackHeapBarrier",
      "shortDesc": "Unfinished Backtranslation",
      "startCol": -1,
      "startLNr": -1,
      "type": "warning"
    },
    ...
]
```


### Configure theme & style
#### Bootstrap theming
Edit [bootstrap_dev/scss/main.scss](bootstrap_dev/scss/main.scss) and then run `npm run css` to apply changes.

### Dependencies
* [ace-editor](https://ace.c9.io/)
* [jquery](https://jquery.com/)
* [handlebars](https://handlebarsjs.com/)
* [bootstrap](https://getbootstrap.com/)
