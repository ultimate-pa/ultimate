package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.IteRemover;


/**
 * Transform term into an equivalent term without ite terms.
 * @author Matthias Heizmann
 */
public class RewriteIte implements PreProcessor {

	@Override
	public Term process(Script script, Term term) {
		return (new IteRemover(script)).transform(term);
	}

	@Override
	public String getDescription() {
		return "Remove ite terms.";
	}
}