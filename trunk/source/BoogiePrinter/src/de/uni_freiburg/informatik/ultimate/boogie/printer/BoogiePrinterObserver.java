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
package de.uni_freiburg.informatik.ultimate.boogie.printer;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.boogie.printer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * @author hoenicke
 */
public class BoogiePrinterObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public BoogiePrinterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final PrintWriter writer = openTempFile(root);
			if (writer != null) {
				final Unit unit = (Unit) root;
				final BoogieOutput output = new BoogieOutput(writer);
				output.printBoogieProgram(unit);
				writer.close();
			}
			return false;
		}
		return true;
	}

	private PrintWriter openTempFile(final IElement root) {
		String path;
		String filename;
		File file;

		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.SAVE_IN_SOURCE_DIRECTORY_LABEL)) {
			final ILocation loc = ILocation.getAnnotation(root);
			final File inputFile = new File(loc.getFileName());
			if (inputFile.isDirectory()) {
				path = inputFile.getPath();
			} else {
				path = inputFile.getParent();
			}
			if (path == null) {
				mLogger.warn("Model does not provide a valid source location, falling back to default dump path...");
				path = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
						.getString(PreferenceInitializer.DUMP_PATH_LABEL);
			}
		} else {
			path = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getString(PreferenceInitializer.DUMP_PATH_LABEL);
		}

		try {
			if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(PreferenceInitializer.UNIQUE_NAME_LABEL)) {
				file = File.createTempFile(
						"BoogiePrinter_" + new File(ILocation.getAnnotation(root).getFileName()).getName() + "_UID",
						".bpl", new File(path));
			} else {
				filename = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
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
			return new PrintWriter(new FileWriter(file));

		} catch (final IOException e) {
			mLogger.fatal("Cannot open file", e);
			return null;
		}
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
