--- HOW TO RUN THE CDT-PLUGIN INSIDE ECLIPSE ---

1. 	Make sure that you have installed Eclipse-RCP and Eclipse-CDT in the right way!
2. 	Open the manifest of this plugin ("META-INF/MANIFEST.MF"), in the upper	
	right corner you should see a the run symbol of Eclipse.
3.	Now you choose "Run as an Eclipse application...", if you press this button
	a new Eclipse instance will open.
4.	You should recognize that this new Eclipse instance is somehow scrambled,
	with some strange GUI-elements. This is because all plugins in the workspace
	are deployed to this new instance. And the strange elements come from the
	"UltimateGUI" plugin. To solve this we disable this plugin for our 
	"Run as Eclipse application" configuration.
5.	To fix this point, go to "Run/Run Configuration...", now you should see there
	a new Run Configuration, its name should be "Eclipse Application" or something
	like that. If you choose this configuration, you should see on the right side
	a tab called "Plug-Ins". Select this tab!
6. 	Now you should see the point "Launch with" and a Dropdown-Box, where "all
	workspace and enabled target platform" is selected. Now you select there 
	"plugins selected below only".
7. 	Now in the box below a lot of plugins will show up. They should be grouped
	under two major points, "Workspace" and "Target Platform". You should select
	both so that every plugin is now selected. Then you simply deselect the
	following plugins from the "Workspace" group.
	- UltimateGui
	- JungBase
	- de.uni_freiburg.informatik.ultimate.output.jungvisualization
	- WebInterface
	- WebUltimateBridge
8.	When you start the Eclipse instance (Run-Button), everything should look ok now.
9.	To start the Ultimate-Verification you simply select a C-Source File and press the
	right mouse button, there you should see the point "Run C/C++ Code Analysis".
	If you choose this point, Ultimate will start the verification. You can observe this
	process in your Base-Eclipse instance, there the Ultimate-Log will show up.
10.	The preferences for the Codan-Ultimate Plugin are located under the Point
	"C/C++ / CodeAnalysis" in the main preferences. There you should see an Ultimate
	group, where the different Result-Types are referenced as problems. Basically
	they use all the same Checker, but in fact these are different problems, with
	different severities (Error, Warning, Info). Of course more problems can be added,
	how to do this read the "docu.txt", there you find some general information about
	how the structure of the plugin looks like.
	
Possible Problem: "OutOfMemory Exception [PermGen]"
	It is not so clear why this happens sometimes, probably it is a problem with
	the java version. To fix this, you simply add the following line to the VM
	arguments in your "Run Configuration": 
	-XX:MaxPermSize=512M
	This simply gives the perm section of the jvm more memory.


--- HOW TO DEPLOY/INSTALL THE CDT-PLUGIN ---
	
	To use this plugin and the Ultimate verification you have to deploy the needed
	plugins (make a jar file out of it) to the plugin folder of your Eclipse installation.
	
	To do this open the manifest file again. Again on the upper right corner there is
	a button called "Export deployable plugins and fragments". After pressing this
	button a dialog will open where can select all plugins which are in the workspace.
	Basically you need the CDTPlugin and Ultimate without the GUI-stuff. So you should
	select all except of the following plugins:
	- UltimateGui
	- JungBase
	- de.uni_freiburg.informatik.ultimate.output.jungvisualization
	- WebInterface
	- WebUltimateBridge
	Now you can directly choose your plugin folder of the Eclipse installation and
	deploy the plugins to this location. Then after a restart of Eclipse the installed
	plugins should be installed correctly.
	