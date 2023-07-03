-startup
plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar
--launcher.library
plugins/org.eclipse.equinox.launcher.gtk.linux.x86_64_1.1.1300.v20200819-0940
-nosplash
-consoleLog
-vmargs
-Dosgi.noShutdown=true
-Dorg.eclipse.jetty.util.log.class=org.eclipse.jetty.util.log.StdErrLog
-DWebBackend.SETTINGS_FILE={{ .Env.ULTIMATE_BACKEND_SETTINGS_FILE }}
