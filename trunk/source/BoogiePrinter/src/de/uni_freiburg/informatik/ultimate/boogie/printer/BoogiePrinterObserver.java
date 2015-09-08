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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.printer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieOutput;

/**
 * @author hoenicke
 */
public class BoogiePrinterObserver implements IUnmanagedObserver {

	private Logger mLogger;

	public BoogiePrinterObserver(Logger logger){
		mLogger = logger;
	}
	
	
	@Override
	public boolean process(IElement root) {
		if (root instanceof Unit) {
			PrintWriter writer = openTempFile(root);
			if (writer != null) {
				Unit unit = (Unit) root;
				BoogieOutput output = new BoogieOutput(writer);
				output.printBoogieProgram(unit);
				writer.close();
			}
			return false;
		}
		return true;
	}

	private PrintWriter openTempFile(IElement root) {

		String path;
		String filename;
		File f;

		if (PreferenceInitializer.getSaveInSourceDirectory()) {
			path = new File(root.getPayload().getLocation().getFileName())
					.getParent();
			if(path == null){
				mLogger.warn("Model does not provide a valid source location, falling back to default dump path...");
				path = PreferenceInitializer.getDumpPath();
			}
		} else {
			path = PreferenceInitializer.getDumpPath();
		}

		try {
			if (PreferenceInitializer.getUseUniqueFilename()) {
				f = File.createTempFile("BoogiePrinter_"
						+ new File(root.getPayload().getLocation()
								.getFileName()).getName() + "_UID", ".bpl",
						new File(path));
			} else {
				filename = PreferenceInitializer.getFilename();
				f = new File(path + File.separatorChar + filename);
				if (f.isFile() && f.canWrite() || !f.exists()) {
					if (f.exists()) {
						mLogger.info("File already exists and will be overwritten: "
								+ f.getAbsolutePath());
					}
					f.createNewFile();
				} else {
					mLogger.warn("Cannot write to: " + f.getAbsolutePath());
					return null;
				}
			}
			mLogger.info("Writing to file " + f.getAbsolutePath());
			return new PrintWriter(new FileWriter(f));

		} catch (IOException e) {
			mLogger.fatal("Cannot open file", e);
			return null;
		}
	}

	@Override
	public void finish() {
		// not required
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		// not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
