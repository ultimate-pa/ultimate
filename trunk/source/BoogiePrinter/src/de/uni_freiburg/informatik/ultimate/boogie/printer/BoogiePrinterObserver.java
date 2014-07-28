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
	public void init() {
		// not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
