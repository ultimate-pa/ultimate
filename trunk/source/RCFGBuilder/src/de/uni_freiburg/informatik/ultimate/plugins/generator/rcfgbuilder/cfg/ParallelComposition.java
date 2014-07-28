package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a set of CodeBlocks of
 * which only one is executed.
 */
public class ParallelComposition extends CodeBlock {

	private static final long serialVersionUID = -221110423926589618L;
	private final CodeBlock[] m_CodeBlocks;
	private final String m_PrettyPrinted;
	private final Map<TermVariable, CodeBlock> m_BranchIndicator2CodeBlock = new HashMap<TermVariable, CodeBlock>();
	private final IUltimateServiceProvider mServices;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CodeBlocks (Parallely Composed)", "PrettyPrintedStatements",
			"TransitionFormula", "OccurenceInCounterexamples" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CodeBlocks (Parallely Composed)") {
			return m_CodeBlocks;
		} else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrinted;
		} else if (field == "TransitionFormula") {
			return m_TransitionFormula;
		} else if (field == "OccurenceInCounterexamples") {
			return m_OccurenceInCounterexamples;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}

	public ParallelComposition(ProgramPoint source, ProgramPoint target, Boogie2SMT boogie2smt,
			IUltimateServiceProvider services, CodeBlock... codeBlocks) {
		super(source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		mServices = services;
		Script script = boogie2smt.getScript();
		this.m_CodeBlocks = codeBlocks;

		String prettyPrinted = "";

		TransFormula[] transFormulas = new TransFormula[codeBlocks.length];
		TransFormula[] transFormulasWithBranchEncoders = new TransFormula[codeBlocks.length];
		TermVariable[] branchIndicator = new TermVariable[codeBlocks.length];
		for (int i = 0; i < codeBlocks.length; i++) {
			if (!(codeBlocks[i] instanceof StatementSequence || codeBlocks[i] instanceof SequentialComposition || codeBlocks[i] instanceof ParallelComposition)) {
				throw new IllegalArgumentException("Only StatementSequence,"
						+ " SequentialComposition, and ParallelComposition supported");
			}
			codeBlocks[i].disconnectSource();
			codeBlocks[i].disconnectTarget();
			prettyPrinted += "PARALLEL" + codeBlocks[i].getPrettyPrintedStatements();
			transFormulas[i] = codeBlocks[i].getTransitionFormula();
			transFormulasWithBranchEncoders[i] = codeBlocks[i].getTransitionFormulaWithBranchEncoders();
			String varname = "LBE" + codeBlocks[i].getSerialNumer();
			Sort boolSort = script.sort("Bool");
			TermVariable tv = script.variable(varname, boolSort);
			branchIndicator[i] = tv;
			m_BranchIndicator2CodeBlock.put(branchIndicator[i], codeBlocks[i]);
			ModelUtils.mergeAnnotations(codeBlocks[i], this);
		}
		// workaround: set annotation with this pluginId again, because it was
		// overwritten by the mergeAnnotations method
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, m_Annotation);
		m_PrettyPrinted = prettyPrinted;

		boolean s_TransformToCNF = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getBoolean(PreferenceInitializer.LABEL_CNF);

		m_TransitionFormula = TransFormula.parallelComposition(mLogger, mServices, this.getSerialNumer(), boogie2smt,
				null, s_TransformToCNF, transFormulas);
		m_TransitionFormulaWithBranchEncoders = TransFormula.parallelComposition(mLogger, mServices,
				this.getSerialNumer(), boogie2smt, branchIndicator, s_TransformToCNF, transFormulasWithBranchEncoders);
		updatePayloadName();
	}

	@Override
	public String getPrettyPrintedStatements() {
		return m_PrettyPrinted;
	}

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		throw new UnsupportedOperationException();
	}

	public Map<TermVariable, CodeBlock> getBranchIndicator2CodeBlock() {
		return m_BranchIndicator2CodeBlock;
	}

	@Override
	public void setTransitionFormula(TransFormula transFormula) {
		throw new UnsupportedOperationException("transition formula is computed in constructor");
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("BeginParallelComposition{");
		for (int i = 0; i < m_CodeBlocks.length; i++) {
			sb.append("ParallelCodeBlock" + i + ": ");
			sb.append(m_CodeBlocks[i]);
		}
		sb.append("}EndParallelComposition");
		return sb.toString();
	}

}
