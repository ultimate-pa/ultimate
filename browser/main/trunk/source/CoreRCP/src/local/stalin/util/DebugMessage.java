package local.stalin.util;

import java.text.MessageFormat;

/**
 * Class used to prevent unnecessary String conversions and 
 * concatenations.
 * 
 * Just use {num} to refer to the array position like in
 * <code>new DebugMessage("Arg 1 is {1} and 0 is {0}",obj0,obj1)</code>.
 * The string is formatted by {@link java.text.MessageFormat}.
 * 
 * @author Juergen Christ
 */
public class DebugMessage {
	private String msg;
	private Object[] params;
	public DebugMessage(String msg, Object... params) {
		this.msg = msg;
		this.params = params;
	}
	public String toString() {
		return MessageFormat.format(msg, params);
	}
}
