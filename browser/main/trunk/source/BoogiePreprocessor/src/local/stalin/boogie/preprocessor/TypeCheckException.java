/**
 * 
 */
package local.stalin.boogie.preprocessor;

/**
 * This exception is thrown by the type checker if there is a type error in the
 * Boogie file.
 * 
 * @author hoenicke
 *
 */
public class TypeCheckException extends RuntimeException {
	private static final long serialVersionUID = -6173384860964538008L;

	public TypeCheckException() {
	}

	public TypeCheckException(String message) {
		super(message);
	}

	public TypeCheckException(Throwable cause) {
		super(cause);
	}

	public TypeCheckException(String message, Throwable cause) {
		super(message, cause);
	}

}
