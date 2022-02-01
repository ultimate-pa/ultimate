
package jdd.util;

import java.io.FileOutputStream;
import java.io.IOException;

// DOT TYPE ARE:
// ps ps2 hpgl pcl mif pic gd gd2 gif jpg jpeg png wbmp ismap imap cmap vrml
// vtx mp fig svg svgz dia dot canon plain plain-ext xdot

/** simple Dot-class that organizes calls to AT&T DOT */

public class Dot {
	// uses in setType
	public static final int TYPE_EPS = 0, TYPE_PNG = 1, TYPE_DOT = 2, TYPE_FIG = 3;
	public static final int TYPE_GIF = 4, TYPE_JPG = 5;

	private static final String DOT_COMMAND = "dot";
	private static final String [] DOT_TYPES = { "ps", "png", "dot", "fig", "gif", "jpg" };
	private static final String GV_COMMAND = "";


	private static Runtime rt = Runtime.getRuntime();
	private static int dot_type = TYPE_PNG; /** output type */
	private static boolean run_dot = true;	/** should we actually execute dot or not? */
	private static boolean remove_dot_file = true;	/** remove the dot file after we are done??*/


	/**
	 * Create a DOT file from a String
	 */
	public static void showString(String file, String string)  {
		try {
			final FileOutputStream fs = new FileOutputStream (file);
			fs.write(string.getBytes() );
			fs.flush();
			fs.close();
			showDot(file);
		} catch(final IOException exx) {
			JDDConsole.out.println("Unable to save graph to the file "+ file + "\nReason: " + exx.toString() );
		}
	}

	/**
	 * Run DOT on this file to produce an image.
	 *
	 * <p>
	 * NOTE: unless you call Dot.setRemoveDotFile(false), the file will be REMOVED
	 * @see #setRemoveDotFile
	 */
	public static void showDot(String file) {

		// first, check for shell characters
		if(FileUtility.invalidFilename(file) ) {
			System.err.println("[Dot] The filename '" + file + "' is invalid.");
			System.err.println("[Dot] Maybe it contains characters we don't like?");
			return;
		}


		try {

			if(run_dot) {
				final String cmd = DOT_COMMAND + " -T" + DOT_TYPES[dot_type] + " \"" + file + "\" -o \"" + file + "." + DOT_TYPES[dot_type] + "\"";
				final Process p = rt.exec(cmd);
				p.waitFor();
			}

			if(remove_dot_file) {
				FileUtility.delete(file);
			}

		} catch(final IOException exx) {
			JDDConsole.out.println("Unable to run DOT on " + file + "\nReason: " + exx.toString() );
		}catch(final InterruptedException exx) {
			JDDConsole.out.println("DOT interrupted when processing " + file + "\nReason: " + exx.toString() );
		}
	}

	public static boolean scaleable() {
		return (dot_type == TYPE_DOT) || (dot_type == TYPE_EPS) || (dot_type == TYPE_FIG);
	}
	public static void setType(int t) { dot_type = t; }
	public static void setExecuteDot(boolean b) { run_dot = b; }
	public static void setRemoveDotFile(boolean b) { remove_dot_file = b; }

}

