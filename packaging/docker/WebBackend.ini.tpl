-startup
plugins/org.eclipse.equinox.launcher_1.6.800.v20240513-1750.jar
--launcher.library
plugins/org.eclipse.equinox.launcher.gtk.linux.x86_64_1.2.1000.v20240506-2123
-nosplash
-consoleLog
-vmargs
-Dosgi.noShutdown=true
-Dorg.eclipse.jetty.util.log.class=org.eclipse.jetty.util.log.StdErrLog
-DWebBackend.SETTINGS_FILE={{ .Env.ULTIMATE_BACKEND_SETTINGS_FILE }}
