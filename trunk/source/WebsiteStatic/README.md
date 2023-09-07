# WebsiteStatic
This is the **Ultimate** framework website. It provides information about the Ultimate framework, its tools, development, awards etc.

The website also includes a web interface front-end for the Ultimate framework web API implemented by ``WebBackend``.
The web interface requires access to a running ``WebBackend`` applications API to run Ultimate jobs.

## 1. Development

The website is built using the static site generator [jekyll](https://jekyllrb.com/).
To build the website, you need to install jekyll. Follow the instructions [here](http://jekyllrb.com/docs/installation/).
Alternatively, you can run jekyll [in a docker container](https://hub.docker.com/r/jekyll/jekyll).

You can start a local server (for development) by running
```sh
jekyll serve
```
The website will then be available under `http://localhost:4000/website/` (the `website/` suffix mirrors the URL when serving the website from `WebBackend`, but can be overriden with the `--baseurl` parameter).

Serving the website in this way is useful for development:
If you make changes to the website source code, jekyll will automatically recompile the website,
and your changes should show up in the browser immediately.

### 1.1 Website Structure

Jekyll configuration can be found in `_config.yml`.

```
WebsiteStatic/
├── _awards                   Awards and medals won by Ultimate in SV-COMP etc.
├── _layouts                  Jekyll layouts wrapped around content (e.g. header, footer)
├── _tools                    Detail pages for the different Ultimate tools
├── bootstrap_dev             see "Configure theme & style" below
├── css                       Style files for the website
├── fonts                     Fonts used by the website
├── img                       Image files used by the website UI
|   └── awards                Photos and graphics for the awards page
├── js
|   ├── vendor                3rd party dependencies
|   └── webinterface          Scripts needed for the web interface
└── webinterface
    ├── code_examples         Code examples that can be selected in the UI
    └── workers               Toolchains and visible settings
```


### 1.2 Configure theme & style

We use [bootstrap](https://getbootstrap.com/) as frontend toolkit (i.e., for styling etc).

In order to modify bootstrap styling, download a node package manager (for Windows, use <https://github.com/coreybutler/nvm-windows/releases>) and run `npm install` in `bootstrap_dev/`.

Edit [bootstrap_dev/scss/main.scss](bootstrap_dev/scss/main.scss) and then run `npm run css` to apply changes.

### 1.3 JavaScript Dependencies
* [ace-editor](https://ace.c9.io/)
* [jquery](https://jquery.com/)
* [handlebars](https://handlebarsjs.com/)
* [bootstrap](https://getbootstrap.com/)


## 2. Adding a new tool

To add a new tool to the website, follow these steps:
- Create an HTML file named after the tool in `_tools/`.
- In the YAML frontmatter at the top of the file (between `---`), declare the metadata for your tool. Take a look at other tools for reference.
- Open `_config.yml` and add your tool to the array in `collections > tools > order`.
  After recompilation (since you edited `_config.yml`, you must restart `jekyll`) the tool should now show up on the website.

### 2.1 Adding your tool to the Web Interface
- In order to have support for your tool in the web interface, you must declare at least one entry in the `languages` array of the tool page's YAML frontmatter.
  Specify the supported input language, and a unique name for the worker (see `Web Interface > Glossary`), typically by combining language and tool name.
- For each worker, add a toolchain XML (with the same name as the worker) in `webinterface/workers/`.
- In `build_all_settings.py`, enter your worker into the `WORKER_SETTINGS` dictionary, and specify the base settings file that should be used.
  Make sure all relevant settings are whitelisted in `WebBackend`.
- If the web interface should display settings to the user, create a file named `<worker>.override.json` in `webinterface/workers/`.
  Here you can specify which settings should be visible.
  You can also give a different `name` for a setting, and for enumeration-based settings you can restrict the available `options` shown in the UI.
- Run `build_all_settings.py` to generate the settings JSON files for your new tool.

## 3. Web Interface
### 3.1 Glossary
* **Tool**: An Ultimate tool, for example "Ultimate Automizer".
  * Defined in [config.js](config/config.js) under the key `tools`.
  * Assigned to a unique `tool.id`.
* **Worker**: Here a selected tool and a selected language. In Ultimate also called a toolchain.
  * Each tool can have multiple workers. A worker is a dictionary in a list of `workers` in a `tools` entry in [config.js](config/config.js)
  * Each worker of the website needs a unique id `id`.
  * Each worker needs a toolchain XML in [ultimate_toolchain_xmls](config/ultimate_toolchain_xmls) named `<id>.xml`

### 3.2 Configuration and Setup
All configuration is set in `config/config.js`.
* Copy [config/config.dist.js](config/config.dist.js) to `config/config.js`.
* Edit `config/config.js` to your needs. The `config/config.dist.js` file is commented to guide the configuration.

### 3.3 Code examples
All code examples for a specific worker are stored in `webinterface/code_examples/<worker.id>`.

To **add or alter examples**:
1. Copy or edit one example in `webinterface/code_examples/<worker.id>/<example_name>`.
2. Go to `webinterface/code_examples` and run `refresh_index.py`

To recreate the initial examples available, go to `webinterface/code_examples` and run `copy_initial_examples.py` and then
 `refresh_index.py`.


### 3.4 Expected result response example

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




