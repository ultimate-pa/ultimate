
package jdd.bdd.debug;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.jre.JREInfo;

/**
 * <pre>
 * This class opens and runs a suite of BDD traces from a zip file.
 * A trace file is assumed to have the '.trace' posfix. Any file with the 'README' posfix
 * is assumed to be an information file and is dumped to stdout.
 *
 * </pre>
 *
 */

public class BDDTraceSuite {

	/**
	 * filename is the name of zip file, initial_size is the suggested "base" for
	 * deciding the initial of the nodetable. if initial_size is -1, it is ignored
	 * and BDDTrace's default value is used
	 */
	public BDDTraceSuite(String filename, int initial_size) {

		try {
			final InputStream  is = new FileInputStream (filename);
			final ZipInputStream zis = new ZipInputStream(is);

			JDDConsole.out.println("\n***** [ " + filename + " ] *****");
			JREInfo.show();

			ZipEntry ze = zis.getNextEntry();
			while(zis.available()!= 0) {

				final String name = ze.getName();

				if(name.endsWith(".trace")) {
					runTrace(name, zis, initial_size);
				} else if(name.endsWith("README")) {
					showFile(name,zis);
				}

				zis.closeEntry();
				ze = zis.getNextEntry();
			}
			zis.close();
			is.close();
		} catch(final IOException exx) {
			JDDConsole.out.println("FAILED: " + exx.getMessage() + "\n");
			exx.printStackTrace();
			System.exit(20);
		}
	}

	private void runTrace(String name, InputStream is, int size) {
		// enable verbose temporary!
		final boolean save = Options.verbose;
		Options.verbose = true;

		System.err.println("Tracing " + name + "...");
		try {
			if(size == -1) {
				new BDDTrace(name, is);
			} else {
				new BDDTrace(name, is, size);
			}
		} catch(final Exception exx) {
			JDDConsole.out.println("FAILED: " + exx.getMessage()  + "\n\n");
			exx.printStackTrace();
		}

		Options.verbose = save;		// set back verbose to its old value

		// let's cleanup, so we dont affect the next run so much:
		for(int i = 0; i < 6; i++) {
			System.gc();
		}

		try { Thread.sleep(5000);  } catch(final Exception ignored) { } // calm down!
	}

	private void showFile(String name, InputStream is) throws IOException {
		JDDConsole.out.println("File " + name);
		final byte [] buffer = new byte[10240];

		for(;;) {
			final int i = is.read(buffer, 0, buffer.length);
			if(i <= 0) {
				return;
			}
			JDDConsole.out.println(new String(buffer, 0, i));
		}
	}

	// -------------------------------------------------------------

	public static void main(String [] args) {
		if( args.length == 1) {
			new BDDTraceSuite(args[0], -1);
		} else if(args.length == 2) {
			new BDDTraceSuite(args[0], Integer.parseInt(args[1]));
		} else {
			System.err.println("Usage: java BDDTraceSuite <trace-suite.zip> [initial size _base_]");
		}
	}
}
