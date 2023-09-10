# WebBackend

The WebBackend project is for serving the Ultimate tools as a web-service.
The WebBackend application runs an embedded jetty to provide an API for executing Ultimate jobs.

## Deploy
Go to `trunk/source/BA_MavenParentUltimate` run `mvn clean install -P materialize`.
After a successful build, the artifacts to run and configure the application can be found in `trunk/source/BA_SiteRepository/target/products/WebBackend`.

There are two main artifacts. The `WebBackend` (described by this README) and the front-end (in the folder `WebsiteStatic`).
* **WebsiteStatic** is a standalone frontend supposed to be served by a web server (e.g. Apache or Nginx). It is plain copy of the `trunk/source/WebsiteStatic` folder. See [trunk/source/WebsiteStatic/README.md](../WebsiteStatic/README.md) for its documentation.
* **WebBackend** contains the backend (this project). It runs the Ultimate framework and listens to incoming API calls from the frontend.

## Configuration

### Initial backend configuration
1. Copy the backend from `trunk/source/BA_SiteRepository/target/products/WebBackend/<plattform>/<ws>/<arch>/` to some folder, e.g. `/opt/Ultimate`.
2. Create the configuration files by copying/renaming the examples:
   * Copy `web.config.properties.dist` to `web.config.properties`
   * Copy `settings_whitelist.json.dist` to `settings_whitelist.json`
  
   Note: config files inside the target directory will be lost on a rebuild.
3. Add the path to your `web.config.properties` to `WebBackend.ini`:

   ```ini
    -DWebBackend.SETTINGS_FILE=C:\path\to\your\web.config.properties
   ```

4. Add the path to the settings whitelist to  `web.config.properties`:

   ```properties
   SETTINGS_WHITELIST=C:\\path\\to\\your\\settings_whitelist.json
   ```

### Changing configuration
There are two ways of changing configuration settings: by editing `web.config.properties` or by specifying VM arguments on the command line.

A setting "`SETTING_FOO`" in `web.config.properties` can be overridden on the command line with `-DWebBackend.SETTING_FOO=bar`.

### Default configuration

``` ini
# DEBUG (bool) .............. : True increases the verbosity of the logs
# PORT (int) ................ : determines the port the jetty server will be listening
# BACKEND_ROUTE (string) .... : The URL prefix, the API will be served at
# E.g. /api results in <http://localhost:PORT/api>
# SETTINGS_WHITELIST (string) : Path to a local user settings whitelist
DEBUG=True
PORT=8080
BACKEND_ROUTE=/api
SETTINGS_WHITELIST=C:\\path\\to\\settings_whitelist.json

# SERVE_WEBSITE (bool) .... : True will also serve the Frontend
# If set to True, FRONTEND_PATH and FRONTEND_ROUTE should be set
# FRONTEND_PATH (string) .. : Path to the `WebsiteStatic` folder containing the Frontend
# FRONTEND_ROUTE (string) . : The URL prefix, the FRONTEND will be served at
# E.g. /website results in <http://localhost:PORT/website>
SERVE_WEBSITE=True
FRONTEND_PATH=C:\\path\\to\\WebsiteStatic
FRONTEND_ROUTE=/website

# LOG_FILE_PATH (string) .. : Absolute (or relative from java.class.path) path to the log file (/dev/stdout and the like is also ok)
# LOG_LEVEL (string) ...... : Logging verbosity. Choose from: ALL, DEBUG, INFO, WARN, OFF
LOG_FILE_PATH=C:\\path\\to\\var\\log\\logfile.log
LOG_LEVEL=INFO
```

### Whitelist for user settings

If API users should be able to change some settings, you have to whitelist them in `settings_whitelist.json`.
There, you can allow or forbid options for plugins. Note that we currently do not restrict values of options. Either you are allowed to set all possible values, or nothing.

Example:

```json
{
 "plugin.id": ["key_foo", "key_bar"],
 "de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker": [
  "remove filename from checker output"
 ],
}
```

Ensure the path to `settings_whitelist.json` is set correctly for the `SETTINGS_WHITELIST` setting.

You can generate `settings_whitelist.json` from a given configuration using the Ultimate command line:

Example:

``` bash
./Ultimate -tc config/AutomizerReach.xml -s config/svcomp-Overflow-64bit-Automizer_Default.epf -i dummy --generate-backend-json-from-delta
...
{"de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator":["Pointer base address is valid at dereference","Check if freed pointer was valid","Check unreachability of error function in SV-COMP mode","If two pointers are subtracted or compared they have the same base address","Check array bounds for arrays that are off heap","Use constant arrays","Check division by zero","Check absence of signed integer overflows","Overapproximate operations on floating types","Checked method. Library mode if empty.","Pointer to allocated memory at dereference"],"de.uni_freiburg.informatik.ultimate.boogie.procedureinliner":["Ignore calls to procedures called more than once"],"de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction":["SMT solver","Looper check in Petri net analysis","Independence relation used for large block encoding in concurrent analysis","Compute Interpolants along a Counterexample","Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG","Command for external solver","Trace refinement strategy","Positions where we compute the Hoare Annotation","Automaton type used in concurrency analysis","Order on configurations for Petri net unfoldings"],"de.uni_freiburg.informatik.ultimate.plugins.blockencoding":["Use SBE","Create parallel compositions if possible"],"de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder":["SMT solver","Size of a code block","Command for external solver"],"de.uni_freiburg.informatik.ultimate.core":["Log level for class"]} 
```

### Serving the front-end (aka `WebsiteStatic`)
After a build, a cleaned, ready to be served Version of the `WebsiteStatic` project can be found in `trunk/source/BA_WebBackend/target/products/WebsiteStatic`.

#### Bundled with the backend
* Set the config-parameter `SERVE_WEBSITE` to `True`.
* Set the config-parameter `FRONTEND_PATH` to the absolute path of the `WebsiteStatic` folder.
* Configure the Website. See `trunk/source/WebsiteStatic/README.md` for details.

#### Stand alone
* Set the config-parameter `SERVE_WEBSITE` to `False`.
* Serve the content of `WebsiteStatic` as a static HTML site from a web server of your choice.
* Configure the Website. See `trunk/source/WebsiteStatic/README.md` for details.

## Start
After configuring, just run `./WebBackend`.
