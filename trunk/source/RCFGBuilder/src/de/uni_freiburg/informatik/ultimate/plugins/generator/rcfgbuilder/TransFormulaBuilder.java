package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;

/**
 * Provides methods to build TransitionsFormulas for the nodes and edges of a
 * recursive control flow graph.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class TransFormulaBuilder {

	// We use Boogie2SMT to translate boogie Statements to SMT formulas
	private final Boogie2SMT m_Boogie2smt;
	private final boolean m_SimplifyCodeBlocks;

	private final IUltimateServiceProvider mServices;

	public TransFormulaBuilder(Boogie2SMT boogie2smt, IUltimateServiceProvider services) {
		mServices = services;
		m_Boogie2smt = boogie2smt;
		m_SimplifyCodeBlocks = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getBoolean(PreferenceInitializer.LABEL_Simplify);
	}

	/**
	 * Add TransitionFormulas to an edge in the recursive control flow graph. If
	 * the edge is a CallEdge or ReturnEdge two formulas are added. One that
	 * represents the local variable assignments one that represents the global
	 * variable assignments. If the edge is an InternalEdge one
	 * TransitionFormula is added. This TransitionFormula represents the effect
	 * of all Assignment, Assume and Havoc Statements of this edge. If the edge
	 * is a GotoEdge or a SummaryEdge no TransitionFormula is added.
	 * 
	 * @param cb
	 *            An IEdge that has to be a CallEdge, InternalEdge, ReturnEdge,
	 *            GotoEdge or SummaryEdge.
	 */
	public void addTransitionFormulas(CodeBlock cb, String procId) {
		Statement[] statements;
		if (cb instanceof StatementSequence) {
			statements = ((StatementSequence) cb).getStatements().toArray(new Statement[0]);
		} else if (cb instanceof Summary) {
			statements = new Statement[] { ((Summary) cb).getCallStatement() };
		} else if (cb instanceof GotoEdge) {
			throw new IllegalArgumentException("Auxiliary Gotos should have" + "been removed.");
		} else {
			throw new AssertionError();
		}

		TransFormula tf = null;
		try {
			tf = m_Boogie2smt.getStatements2TransFormula().statementSequence(m_SimplifyCodeBlocks, procId, statements);
		} catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				reportUnsupportedSyntax(cb, e.getMessage());
			}
			throw e;
		}
		cb.setTransitionFormula(tf);
	}

	void reportUnsupportedSyntax(CodeBlock cb, String longDescription) {
		ILocation loc = cb.getPayload().getLocation();
		SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME, loc, longDescription);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}
}
