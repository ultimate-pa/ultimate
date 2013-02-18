package local.stalin.nativez3;

/**
 * Class used to throw an exception whenever an operation on native Z3 fails.
 * 
 * @author Juergen Christ
 */
@SuppressWarnings("serial")
public class Z3Exception extends Exception {
	
	private int merror;
	private String merrmsg;
	
	private Z3Exception(int error,String errmsg) {
		merror = error;
		merrmsg = errmsg;
	}
	
	public String toString() {
		return "Z3 error " + merror + ": " + merrmsg;
	}
	
}
