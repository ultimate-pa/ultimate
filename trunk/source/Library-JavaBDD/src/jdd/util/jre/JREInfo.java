
package jdd.util.jre;

import java.util.Date;
import java.util.Properties;

import jdd.util.JDDConsole;
import jdd.util.math.Digits;


/**
 * <pre>
 * print some info about the JRE...
 * </pre>
 */
public class JREInfo {
	public static Runtime rt = Runtime.getRuntime();

	public static long usedMemory() { return  rt.totalMemory() - rt.freeMemory(); }
	public static long totalMemory() { return  rt.totalMemory(); }
	public static long freeMemory() { return rt.freeMemory(); }
	public static long maxMemory() { return rt.maxMemory(); }


	/** print out some info about the system and JVM etc. */
	public static void show() {
		final Properties prop = System.getProperties();
            
		JDDConsole.out.println("Using JDD build " + jdd.Version.build +" on " + (new Date()).toString() + "\n");
		JDDConsole.out.print("Using " + prop.getProperty("java.vendor") + " JRE " + prop.getProperty("java.version"));
		final String jit = prop.getProperty("java.compiler");
		if(jit != null) {
			JDDConsole.out.print(", " + jit +  " JIT in");
		}
		JDDConsole.out.println(" "+ prop.getProperty("java.vm.name") );

		JDDConsole.out.println("OS " + prop.getProperty("os.name") + " on " + rt.availableProcessors() + " " + prop.getProperty("os.arch") + " CPU(s)");
		JDDConsole.out.print("Total JRE memory: " ); Digits.printNumber1024(rt.maxMemory());
		JDDConsole.out.print(", memory currently reserved by the JRE: " ); Digits.printNumber1024(usedMemory());
		JDDConsole.out.println("\n");
	}

	public static void main(String [] args) {
		show();
	}
}



