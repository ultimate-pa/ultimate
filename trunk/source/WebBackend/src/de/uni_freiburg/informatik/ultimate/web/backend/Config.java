package de.uni_freiburg.informatik.ultimate.web.backend;

import java.io.FileInputStream;
import java.io.IOError;
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.util.Properties;
import java.util.function.Function;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * @formatter:off
 * WebBackend settings.
 *
 * # Available settings:
 * Config.DEBUG	.......... // (bool) If true be more verbose.
 * Config.SERVE_WEBSITE .. // (bool) If true, the static front-end will be served at http://host:Config.PORT/Config.FRONTEND_ROUTE
 * Config.PORT ........... // (int) Port Jetty will be serving at.
 * Config.FRONTEND_PATH .. // (string) absolute path to the front-end root directory (/trunk/source/WebsiteStatic) in ultimate repo.
 * Config.FRONTEND_ROUTE . // (string) The URL slug the front-end will be served at (e.g. http://host:Config.PORT/website).
 * Config.BACKEND_ROUTE .. // (string) The URL slug the back-end will be served at (e.g. http://host:Config.PORT/api).
 *
 * # How to change settings.
 * 	1. Uses default setting constants as defined here.
 * 	2. Overrides settings provided by a "web.config.properties" file.
 * 	3. Overrides settings provided by VM arguments e.g.:
 * 		--DWebBackend.DEBUG=false
 * 		--DWebBackend.PORT=8080
 * 		--DWebBackend.SERVE_WEBSITE=true
 * 		--DWebBackend.FRONTEND_PATH="path/to/trunk/source/WebsiteStatic"
 * 		--DWebBackend.FRONTEND_ROUTE="/website"
 * 		--DWebBackend.BACKEND_ROUTE="/api"
 * 		--DWebBackend.SETTINGS_WHITELIST="/path/to/your/settings_whitelist.json"
 * @formatter:on
 */
public class Config {

	private static final Logger LOGGER = LogManager.getLogger();

	private Config() {
		// do not instantiate config class
	}

	public static boolean DEBUG = true;
	public static boolean SERVE_WEBSITE = true;
	public static int PORT = 8080;
	public static String FRONTEND_PATH = "website_static";
	public static String FRONTEND_ROUTE = "/website";
	public static String BACKEND_ROUTE = "/api";
	public static String SETTINGS_WHITELIST = "settings_whitelist.json";
	public static UserSettingsWhitelist USER_SETTINGS_WHITELIST;
	public static String LOG_FILE_PATH = "ultimate_web_backend.log";
	public static String LOG_LEVEL = "INFO";
	public static String TMP_DIR = "";
	public static int FORCED_TIMEOUT = 90;

	private static final String SETTINGS_FILE = "web.config.properties";
	private static final String PROPERTY_PREFIX = "WebBackend.";

	private static final Properties APP_SETTINGS = new Properties();

	/**
	 * Load settings from web.config.properties file
	 */
	public static void load() {
		loadSettingsFile();
		loadSettings();
	}

	public static Path tryGetAbsolutePath(String path) {

		try {
			return FileSystems.getDefault().getPath(path).normalize().toAbsolutePath().normalize();
		} catch (final InvalidPathException | IOError | SecurityException ex) {
			LOGGER.warn(String.format("Could not convert %s to absolute path: %s", path, ex.getMessage()));
		}
		return null;
	}

	/**
	 * Load settings file into Properties object.
	 */
	private static void loadSettingsFile() {
		final String settingsFilePath = loadString("SETTINGS_FILE", SETTINGS_FILE);
		final Path absolutePath = tryGetAbsolutePath(settingsFilePath);
		if (absolutePath == null) {
			LOGGER.warn(String.format("Could not load settings file from '%s', using defaults", settingsFilePath));
			return;
		}

		try (final FileInputStream fileInputStream = new FileInputStream(absolutePath.toFile())) {
			APP_SETTINGS.load(fileInputStream);
			LOGGER.info(String.format("Loaded settings file from %s", settingsFilePath));
		} catch (final IOException e) {
			LOGGER.warn(String.format("Could not load settings file from '%s', using defaults", settingsFilePath));
			LOGGER.warn(e.getMessage());
		}
	}

	/**
	 * Load available settings. Overrides the defaults by the results if any.
	 */
	private static void loadSettings() {
		DEBUG = loadBoolean("DEBUG", DEBUG);
		SERVE_WEBSITE = loadBoolean("SERVE_WEBSITE", SERVE_WEBSITE);
		PORT = loadInteger("PORT", PORT);
		FRONTEND_PATH = loadString("FRONTEND_PATH", FRONTEND_PATH);
		FRONTEND_ROUTE = loadString("FRONTEND_ROUTE", FRONTEND_ROUTE);
		BACKEND_ROUTE = loadString("BACKEND_ROUTE", BACKEND_ROUTE);
		SETTINGS_WHITELIST = loadString("SETTINGS_WHITELIST", SETTINGS_WHITELIST);
		USER_SETTINGS_WHITELIST = new UserSettingsWhitelist(loadString("SETTINGS_WHITELIST", SETTINGS_WHITELIST));
		LOG_FILE_PATH = loadString("LOG_FILE_PATH", LOG_FILE_PATH);
		LOG_LEVEL = loadString("LOG_LEVEL", LOG_LEVEL);
		FORCED_TIMEOUT = loadInteger("FORCED_TIMEOUT", FORCED_TIMEOUT);
		try {
			TMP_DIR = loadPathString("TMP_DIR", Files.createTempDirectory("ultimate_webbackend").toString());
		} catch (final IOException ex) {
			throw new RuntimeException(ex);
		}
	}

	private static <T> T loadObject(final String propertyName, final T defaultValue,
			final Function<Object, T> converter) {
		final Object sysPropertyResult = System.getProperty(PROPERTY_PREFIX + propertyName);
		if (sysPropertyResult != null) {
			return converter.apply(sysPropertyResult);
		}
		final Object appSettingResult = APP_SETTINGS.get(propertyName);
		if (appSettingResult != null) {
			return converter.apply(appSettingResult);
		}
		return defaultValue;
	}

	private static String loadPathString(final String propertyName, final String defaultValue) {
		final String path = loadObject(propertyName, defaultValue, String.class::cast);
		if (Files.exists(Path.of(path))) {
			return path;
		}
		return "";
	}

	/**
	 * Load the setting string named `propertyName`. Returns `defaultValue` if setting is not found. Prefers vmArguments
	 * before settings file.
	 *
	 * @param propertyName
	 * @param defaultValue
	 * @return
	 */
	private static String loadString(final String propertyName, final String defaultValue) {
		return loadObject(propertyName, defaultValue, String.class::cast);
	}

	/**
	 * Load the setting boolean named `propertyName`. Returns `defaultValue` if setting is not found. Prefers
	 * vmArguments before settings file.
	 *
	 * @param propertyName
	 * @param defaultValue
	 * @return
	 */
	private static boolean loadBoolean(final String propertyName, final boolean defaultValue) {
		return loadObject(propertyName, defaultValue, a -> Boolean.parseBoolean((String) a));
	}

	/**
	 * Load the setting integer named `propertyName`. Returns `defaultValue` if setting is not found. Prefers
	 * vmArguments before settings file.
	 *
	 * @param propertyName
	 * @param defaultValue
	 * @return
	 */
	private static int loadInteger(final String propertyName, final Integer defaultValue) {
		return loadObject(propertyName, defaultValue, a -> Integer.parseInt((String) a));
	}
}
