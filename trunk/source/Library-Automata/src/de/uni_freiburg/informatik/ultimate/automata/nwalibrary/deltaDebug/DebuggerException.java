package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

/**
 * Fresh exception type for the debugger.
 * 
 * In order to prevent several causes for the designated error, this exception
 * can be thrown at the respective position to make sure the debugger looks
 * for the correct error position.
 * Of course, a user can specify new types of exceptions as well.
 * 
 * NOTE: After debugging the exception should be removed again, so that the
 * invariant that this exception is thrown at most once in the whole library
 * holds.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
class DebuggerException extends Exception {
	private static final long serialVersionUID = 1L;
	
	final Class<?> m_classOfThrower;
	final String m_message;
	
	public DebuggerException(final Class<?> thrower, final String message) {
		m_classOfThrower = thrower;
		m_message = message;
	}
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append(this.getClass().getSimpleName());
		b.append("(");
		b.append(m_classOfThrower);
		b.append(" : ");
		b.append(m_message);
		b.append(")");
		return b.toString();
	}
}