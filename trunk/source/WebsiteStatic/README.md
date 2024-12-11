# WebsiteStatic
This is the **Ultimate** framework website. It provides information about the Ultimate framework, its tools, development, awards etc.

The website also includes a web interface for the Ultimate framework web API implemented by `WebBackend`.
The web interface requires access to a running `WebBackend` applications API to run Ultimate jobs.

## 1. Development

The website is built using the static site generator [jekyll](https://jekyllrb.com/).
To build the website, you need to install jekyll. Follow the instructions [here](http://jekyllrb.com/docs/installation/).
Alternatively, you can run jekyll [in a docker container](https://hub.docker.com/r/jekyll/jekyll).

To build the website from scratch, run the following script:
```
./scripts/build.py
```
This will perform several build steps (primarily to setup the webinterface support) and then build the website with jekyll.

For production builds (before deploying the website), run the following command instead:
```
./scripts/build.py --production
```

If you only make changes to the HTML content, you do not have to run the full build script above every time.
Instead, you can start a local jekyll server (for development) by running

```sh
jekyll serve
```
The website will then be available under `http://localhost:4000/website/`.
The `website/` suffix mirrors the URL when serving the website from `WebBackend`, but can be overriden with the `--baseurl` parameter.
For instance, the following command will serve the website from `http://localhost:4000/`:
```sh
jekyll serve --baseurl "/"
```
Serving the website in this way is useful for development:
If you make changes to the website source code, jekyll will automatically recompile the website,
and your changes should show up in the browser immediately.


### 1.1 Website Structure

Jekyll configuration can be found in `_config.yml`.

```
WebsiteStatic/
├── _awards/                  Awards and medals won by Ultimate in SV-COMP etc. (see _awards/README.md for details)
├── _layouts/                 Jekyll layouts wrapped around content (e.g. header, footer)
├── _tools/                   Detail pages for the different Ultimate tools (see _tools/README.md for details)
├── bootstrap_dev/            see "Configure theme & style" below
├── css/                      Style files for the website
├── fonts/                    Fonts used by the website
├── img/                      Image files used by the website UI
|   └── awards/               Photos and graphics for the awards page
├── js/
|   ├── vendor/               3rd party dependencies
|   └── webinterface/         Javascript needed for the web interface
├── webinterface/
|   ├── code_examples         Code examples that can be selected in the UI
|   └── workers               Toolchains and visible settings
└── scripts/                  Python scripts for building the website
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
- In `scripts/webinterface/build_all_settings.py`, enter your worker into the `WORKER_SETTINGS` dictionary, and specify the base settings file that should be used.
  Make sure all relevant settings are whitelisted in `WebBackend`.
- If the web interface should display settings to the user, create a file named `<worker>.override.json` in `webinterface/workers/`.
  Here you can specify which settings should be visible.
  You can also give a different `name` for a setting, and for enumeration-based settings you can restrict the available `options` shown in the UI.
- Run `scripts/webinterface/build_all_settings.py` to generate the settings JSON files for your new tool.


## 3. Web Interface

### 3.1 Glossary
- **Tool**: An Ultimate tool, for example "Ultimate Automizer".
  * Defined by a description and metadata in `_tools/<toolname>.html`
  * Assigned to a unique `tool_id`.
  * May be runnable via the web interface.
- **Worker**: Consists of a selected tool and a selected language.
  * Each tool can have multiple workers. They are listed in the `languages` array of the tool definition.
  * Each worker needs a toolchain XML in [ultimate_toolchain_xmls](config/ultimate_toolchain_xmls) named `<id>.xml`
  * You must specify a settings file for each worker in the `WORKER_SETTINGS` dictionary in `scripts/webinterface/build_all_settings.py`.

### 3.2 Configuration and Setup
All configuration is set in `config/config.js`.
- Copy [config/config.dist.js](config/config.dist.js) to `config/config.js`.
- Edit `config/config.js` to your needs. The `config/config.dist.js` file is commented to guide the configuration.

### 3.3 Code examples
The code examples for a specific worker are defined in the `tool_examples_map` dictionary of `./scripts/webinterface/copy_examples.py`.
To **add or alter examples**, edit this dictionary, and run
```
./scripts/webinterface/copy_examples.py
./scripts/webinterface/refresh_index.py
```

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




