package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * Abstract Superclass for lasso extraction. Can be removed if there is only
 * one class that implements this.
 * @author Matthias Heizmann
 */
public abstract class AbstractLassoExtractor {
	protected NestedWord<CodeBlock> m_Stem;
	protected NestedWord<CodeBlock> m_Loop;
	protected ProgramPoint m_Honda;
	protected boolean m_LassoFound;
	protected RCFGNode m_SomeNoneForErrorReport;
	
	public NestedWord<CodeBlock> getStem() {
		if (!m_LassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}
		return m_Stem;
	}

	public NestedWord<CodeBlock> getLoop() {
		if (!m_LassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}

		return m_Loop;
	}

	public ProgramPoint getHonda() {
		if (!m_LassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}

		return m_Honda;
	}

	public boolean wasLassoFound() {
		return m_LassoFound;
	}

	public RCFGNode getSomeNoneForErrorReport() {
		if (m_LassoFound) {
			throw new UnsupportedOperationException(
					"lasso was found, there was no error");
		}
		return m_SomeNoneForErrorReport;
	}
	
}