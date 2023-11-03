package de.uni_freiburg.informatik.ultimate.web.backend;

import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.Map;
import java.util.Set;

import org.eclipse.jetty.util.log.Log;

import com.google.gson.Gson;
import com.google.gson.JsonSyntaxException;
import com.google.gson.reflect.TypeToken;
import com.google.gson.stream.JsonReader;

public class UserSettingsWhitelist {

	private Map<String, Set<String>> mWhitelist;

	public UserSettingsWhitelist(final String filePath) {
		initFromFile(filePath);
	}

	/**
	 * Check if "pluginId" is available in the whitelist.
	 *
	 * @param pluginId
	 * @return
	 */
	public boolean isPluginIdCovered(final String pluginId) {
		return mWhitelist.containsKey(pluginId);
	}

	/**
	 * Check if "pluginId" has white-listed "key".
	 *
	 * @param pluginId
	 * @param key
	 * @return
	 */
	public boolean isPluginKeyWhitelisted(final String pluginId, final String key) {
		return getPluginKeys(pluginId).contains(key);
	}

	private Set<String> getPluginKeys(final String pluginId) {
		final Set<String> keys = mWhitelist.get(pluginId);
		if (keys == null) {
			return Collections.emptySet();
		}
		return keys;
	}

	private void initFromFile(final String filePath) {
		final Path file = Paths.get(filePath);
		if (Files.notExists(file)) {
			mWhitelist = Collections.emptyMap();
			Log.getRootLogger().warn(String.format(
					"Could not load user settings whitelist from %s because the file or path does not exist", file));
		} else {
			try (final JsonReader jsonReader = new JsonReader(new FileReader(file.toFile()))) {
				mWhitelist = new Gson().fromJson(jsonReader, new TypeToken<Map<String, Set<String>>>() {
				}.getType());
				Log.getRootLogger().info("Loaded user settings whitelist");
			} catch (IOException | JsonSyntaxException e) {
				Log.getRootLogger().warn(
						String.format("Could not load user settings whitelist from %s: %s", filePath, e.getMessage()));
				mWhitelist = Collections.emptyMap();
			}
		}
	}
}
