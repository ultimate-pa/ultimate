/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.util;

import java.io.File;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class FilePrinterUtils {
	private FilePrinterUtils() {
		// static utility class cannot be instantiated
	}

	private static final String SAVE_IN_SOURCE_DIRECTORY_LABEL = "Save file in source directory";
	private static final String AUTOMATIC_NAMING_LABEL = "Use automatic naming";
	private static final String OUTPUT_DIRECTORY_LABEL = "Output directory";
	private static final String OUTPUTFILE_NAME_LABEL = "Output file name";

	public static UltimatePreferenceItem<?>[] getPrinterPreferences(final String defaultFileName) {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(OUTPUT_DIRECTORY_LABEL, System.getProperty("java.io.tmpdir"),
						PreferenceType.Directory),
				new UltimatePreferenceItem<>(OUTPUTFILE_NAME_LABEL, defaultFileName, PreferenceType.String),
				new UltimatePreferenceItem<>(SAVE_IN_SOURCE_DIRECTORY_LABEL, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(AUTOMATIC_NAMING_LABEL, false, PreferenceType.Boolean),

		};
	}

	public record OutputFileSettings(boolean saveInSourceDirectory, boolean automaticNaming, String outputDirectory,
			String outputFileName, String automaticPrefix, String automaticSuffix, String automaticExtension) {
		// simple record, typically populated from preferences (and fixed prefix, suffix and extension)

		public static OutputFileSettings fromPrinterPreferences(final IPreferenceProvider prefs,
				final String automaticPrefix, final String automaticSuffix, final String automaticExtension) {
			return new OutputFileSettings(
					// preference-based settings
					prefs.getBoolean(SAVE_IN_SOURCE_DIRECTORY_LABEL), prefs.getBoolean(AUTOMATIC_NAMING_LABEL),
					prefs.getString(OUTPUT_DIRECTORY_LABEL), prefs.getString(OUTPUTFILE_NAME_LABEL),

					// fixed prefix, suffix and extension
					automaticPrefix, automaticSuffix, automaticExtension);
		}
	}

	public static File openOutputFile(final OutputFileSettings settings, final IElement root, final ILogger logger) {
		return openOutputFile(settings, ILocation.getAnnotation(root).getFileName(), logger);
	}

	public static File openOutputFile(final OutputFileSettings settings, final String inputFileName,
			final ILogger logger) {
		final String path = getDumpPath(settings, inputFileName, logger);
		if (settings.automaticNaming()) {
			try {
				return File.createTempFile(
						settings.automaticPrefix() + new File(inputFileName).getName() + settings.automaticSuffix(),
						settings.automaticExtension(), new File(path));
			} catch (final IOException e) {
				logger.fatal("Could not create temporary file");
				throw new IllegalStateException("Could not create temporary file", e);
			}
		}

		final File file = new File(path + File.separatorChar + settings.outputFileName());

		if (file.exists()) {
			if (!file.isFile() || !file.canWrite()) {
				logger.fatal("Cannot write to " + file.getAbsolutePath());
				throw new IllegalStateException("Cannot write to " + file.getAbsolutePath());
			}
			logger.warn("File already exists and will be overwritten: " + file.getAbsolutePath());
			return file;
		}

		// As the file does not yet exist, try to create it.
		try {
			file.createNewFile();
		} catch (final IOException e) {
			logger.fatal("Could not create file: " + file.getAbsolutePath(), e);
			throw new IllegalStateException("Could not create file: " + file.toString(), e);
		}
		return file;
	}

	private static String getDumpPath(final OutputFileSettings settings, final String inputFileName,
			final ILogger logger) {
		if (settings.saveInSourceDirectory()) {
			final File inputFile = new File(inputFileName);
			final String path = inputFile.isDirectory() ? inputFile.getPath() : inputFile.getParent();
			if (path != null) {
				return path;
			}
			logger.warn("Model does not provide a valid source location, falling back to output directory %s",
					settings.outputDirectory());
		}
		return settings.outputDirectory();
	}
}
