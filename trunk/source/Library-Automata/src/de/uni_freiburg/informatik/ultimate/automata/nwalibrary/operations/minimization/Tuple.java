package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

/**
 * A tuple class for integers.
 */
// TODO Change visibility?
public final class Tuple {
	/**
	 * The first integer.
	 */
	final int m_first;
	/**
	 * The second integer.
	 */
	final int m_second;

	/**
	 * Constructor.
	 * 
	 * @param first
	 *            first state
	 * @param second
	 *            second state
	 */
	public Tuple(final int first, final int second) {
		assert (first < second) : "The first entry must be the smaller one";
		m_first = first;
		m_second = second;
	}

	// TODO: What is a good hash function?
	public int hashCode() {
		return m_first + 17 * m_second;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof Tuple)) {
			return false;
		}
		final Tuple o = (Tuple) other;
		return (o.m_first == this.m_first) && (o.m_second == this.m_second);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("(");
		builder.append(m_first);
		builder.append(", ");
		builder.append(m_second);
		builder.append(")");
		return builder.toString();
	}
}
