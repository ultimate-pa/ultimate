
package jdd.util;

/**
 * A print-target is where text can be printed to, checkout JDDConsole.out,
 * where all JDD output ends up
 */
public interface PrintTarget {
	void println(String str);
	void println();
	void print(String str);
	void print(char c);

	void flush();
}
