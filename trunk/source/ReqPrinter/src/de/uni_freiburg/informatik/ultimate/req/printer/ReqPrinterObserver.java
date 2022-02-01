/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePrinter plug-in.
 *
 * The ULTIMATE BoogiePrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePrinter plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Boogie printer observer.
 */
package de.uni_freiburg.informatik.ultimate.req.printer;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PatternContainer;
import de.uni_freiburg.informatik.ultimate.req.printer.preferences.PreferenceInitializer;

/**
 * @author hoenicke
 */
public class ReqPrinterObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public ReqPrinterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final PatternContainer container = PatternContainer.getAnnotation(root);
			if (container == null) {
				mLogger.warn("No requirements found");
				return false;
			}
			final List<PatternType> pattern = new ArrayList<>(container.getPatterns());
			printPatternList(root, pattern);
			return false;
		} else if (root instanceof ObjectContainer) {
			if (((ObjectContainer) root).getValue() instanceof List) {
				final List<PatternType> pattern = (List<PatternType>) ((ObjectContainer) root).getValue();
				printPatternList(root, pattern);
			}
			return false;
		}
		return true;
	}

	private void printPatternList(final IElement root, final List<PatternType> sortedPatterns) {
		final PrintWriter writer = openTempFile(root);
		sortedPatterns.sort(new Comparator<PatternType>() {

			@Override
			public int compare(final PatternType o1, final PatternType o2) {
				if (o1 instanceof InitializationPattern) {
					if (o2 instanceof InitializationPattern) {
						final VariableCategory o1cat = ((InitializationPattern) o1).getCategory();
						final VariableCategory o2cat = ((InitializationPattern) o2).getCategory();
						if (o1cat == VariableCategory.CONST && o2cat != VariableCategory.CONST) {
							return -1;
						} else if (o2cat == VariableCategory.CONST && o1cat != VariableCategory.CONST) {
							return 1;
						}
					} else {
						return -1;
					}
				} else if (o2 instanceof InitializationPattern) {
					return 1;
				}
				return o1.getId().compareToIgnoreCase(o2.getId());
			}
		});

		for (final PatternType pattern : sortedPatterns) {
			writer.println(pattern.toString());
		}
		writer.close();
	}

	private PrintWriter openTempFile(final IElement root) {
		final String path = getPath(root);
		try {
			final File file;
			if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(PreferenceInitializer.UNIQUE_NAME_LABEL)) {
				file = File.createTempFile(
						ReqPrinter.class.getSimpleName() + "_"
								+ new File(ILocation.getAnnotation(root).getFileName()).getName() + "_UID",
						".req", new File(path));
			} else {
				final String filename = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
						.getString(PreferenceInitializer.FILE_NAME_LABEL);
				file = new File(path + File.separatorChar + filename);
				if ((!file.isFile() || !file.canWrite()) && file.exists()) {
					mLogger.warn("Cannot write to: " + file.getAbsolutePath());
					return null;
				}

				if (file.exists()) {
					mLogger.info("File already exists and will be overwritten: " + file.getAbsolutePath());
				}
				file.createNewFile();
			}
			mLogger.info("Writing to file " + file.getAbsolutePath());
			return new PrintWriter(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file))), false);

		} catch (final IOException e) {
			mLogger.fatal("Cannot open file", e);
			return null;
		}
	}

	private String getPath(final IElement root) {
		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.SAVE_IN_SOURCE_DIRECTORY_LABEL)) {
			final ILocation loc = ILocation.getAnnotation(root);
			final File inputFile = new File(loc.getFileName());
			final String path;
			if (inputFile.isDirectory()) {
				path = inputFile.getPath();
			} else {
				path = inputFile.getParent();
			}
			if (path != null) {
				return path;
			}
			mLogger.warn("Model does not provide a valid source location, falling back to default dump path...");
		}
		return mServices.getPreferenceProvider(Activator.PLUGIN_ID).getString(PreferenceInitializer.DUMP_PATH_LABEL);
	}

	@Override
	public void finish() {
		// not required
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
