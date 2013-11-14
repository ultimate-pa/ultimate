package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class is the abstract superclass of all proof node converters.
 * 
 * @author Christian Schilling
 */
public abstract class AConverter {
	// appendable
	final Appendable m_appendable;
	// theory
	final Theory m_theory;
	// term converter
	final TermConverter m_converter;
	// computation simplifier
	final ComputationSimplifier m_simplifier;
	
	/* prefixes */
	
	// prefix resolution lemmata use
	protected static final String RESOLUTION_LEMMA_PREFIX = "res";
	
	// prefix LA lemmata use
	protected static final String LA_LEMMA_PREFIX = "la";
	
	// prefix CC sub-lemmata use
	protected static final String CC_LEMMA_PREFIX = "cc";
	
	// prefix some rewrite rules use
	protected static final String REWRITE_PREFIX = "rw";
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public AConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier) {
		m_appendable = appendable;
		m_theory = theory;
		m_converter = converter;
		m_simplifier = simplifier;
	}
	
	/**
	 * This method writes a string to the appendable.
	 * 
	 * @param string string that is written
	 * @throws RuntimeException thrown if an IOException is caught
	 */
	protected void writeString(String string) {
		try {
			m_appendable.append(string);
        } catch (IOException e) {
            throw new RuntimeException("Appender throws IOException", e);
        }
	}
}