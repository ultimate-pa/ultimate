/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a set of CodeBlocks of
 * which only one is executed.
 */
public class ParallelComposition extends CodeBlock {

	private static final long serialVersionUID = -221110423926589618L;
	private final List<CodeBlock> m_CodeBlocks;
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

	ParallelComposition(int serialNumber, ProgramPoint source, ProgramPoint target, Boogie2SMT boogie2smt,
			IUltimateServiceProvider services, List<CodeBlock> codeBlocks) {
		super(serialNumber, source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		mServices = services;
		Script script = boogie2smt.getScript();
		this.m_CodeBlocks = codeBlocks;

		String prettyPrinted = "";

		TransFormula[] transFormulas = new TransFormula[codeBlocks.size()];
		TransFormula[] transFormulasWithBranchEncoders = new TransFormula[codeBlocks.size()];
		TermVariable[] branchIndicator = new TermVariable[codeBlocks.size()];
		for (int i = 0; i < codeBlocks.size(); i++) {
			if (!(codeBlocks.get(i) instanceof StatementSequence || codeBlocks.get(i) instanceof SequentialComposition || 
					codeBlocks.get(i) instanceof ParallelComposition || codeBlocks.get(i) instanceof GotoEdge)) {
				throw new IllegalArgumentException("Only StatementSequence,"
						+ " SequentialComposition, ParallelComposition, and GotoEdge supported");
			}
			codeBlocks.get(i).disconnectSource();
			codeBlocks.get(i).disconnectTarget();
			prettyPrinted += "PARALLEL" + codeBlocks.get(i).getPrettyPrintedStatements();
			transFormulas[i] = codeBlocks.get(i).getTransitionFormula();
			transFormulasWithBranchEncoders[i] = codeBlocks.get(i).getTransitionFormulaWithBranchEncoders();
			String varname = "LBE" + codeBlocks.get(i).getSerialNumer();
			Sort boolSort = script.sort("Bool");
			TermVariable tv = script.variable(varname, boolSort);
			branchIndicator[i] = tv;
			m_BranchIndicator2CodeBlock.put(branchIndicator[i], codeBlocks.get(i));
			ModelUtils.copyAnnotations(codeBlocks.get(i), this);
		}
		// workaround: set annotation with this pluginId again, because it was
		// overwritten by the mergeAnnotations method
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, m_Annotation);
		m_PrettyPrinted = prettyPrinted;

		boolean s_TransformToCNF = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getBoolean(RcfgPreferenceInitializer.LABEL_CNF);

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
		for (int i = 0; i < m_CodeBlocks.size(); i++) {
			sb.append("ParallelCodeBlock" + i + ": ");
			sb.append(m_CodeBlocks.get(i));
		}
		sb.append("}EndParallelComposition");
		return sb.toString();
	}

	public List<CodeBlock> getCodeBlocks() {
		return Collections.unmodifiableList(m_CodeBlocks);
	}

}
