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

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Edge in a recursive control flow graph that represents a set of CodeBlocks of which only one is executed.
 */
public class ParallelComposition extends CodeBlock implements IIcfgInternalTransition<IcfgLocation> {

	private static final long serialVersionUID = -221110423926589618L;
	private final List<CodeBlock> mCodeBlocks;
	private String mPrettyPrinted;
	private final Map<TermVariable, CodeBlock> mBranchIndicator2CodeBlock = new HashMap<>();
	private final IUltimateServiceProvider mServices;

	ParallelComposition(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final ManagedScript mgdScript, final IUltimateServiceProvider services, final List<CodeBlock> codeBlocks,
			final XnfConversionTechnique xnfConversionTechnique) {
		super(serialNumber, source, target, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		mServices = services;
		final Script script = mgdScript.getScript();
		mCodeBlocks = codeBlocks;
		mPrettyPrinted = null;

		final UnmodifiableTransFormula[] transFormulas = new UnmodifiableTransFormula[codeBlocks.size()];
		final UnmodifiableTransFormula[] transFormulasWithBranchEncoders =
				new UnmodifiableTransFormula[codeBlocks.size()];
		final TermVariable[] branchIndicator = new TermVariable[codeBlocks.size()];

		for (int i = 0; i < codeBlocks.size(); ++i) {
			final CodeBlock currentCodeblock = codeBlocks.get(i);
			if (!(currentCodeblock instanceof StatementSequence || currentCodeblock instanceof SequentialComposition
					|| currentCodeblock instanceof ParallelComposition || currentCodeblock instanceof GotoEdge)) {
				throw new IllegalArgumentException("Only StatementSequence,"
						+ " SequentialComposition, ParallelComposition, and GotoEdge supported, but got "
						+ currentCodeblock.getClass().getSimpleName());
			}

			if (currentCodeblock.getNumberOfOpenCalls() != 0) {
				throw new IllegalArgumentException("No open calls allowed");
			}

			currentCodeblock.disconnectSource();
			currentCodeblock.disconnectTarget();
			transFormulas[i] = currentCodeblock.getTransformula();
			transFormulasWithBranchEncoders[i] = currentCodeblock.getTransitionFormulaWithBranchEncoders();
			final String varname = "LBE" + currentCodeblock.getSerialNumber();
			final Sort boolSort = SmtSortUtils.getBoolSort(script);
			final TermVariable tv = script.variable(varname, boolSort);
			branchIndicator[i] = tv;
			mBranchIndicator2CodeBlock.put(branchIndicator[i], currentCodeblock);
			ModelUtils.copyAnnotations(currentCodeblock, this);
		}

		// workaround: set annotation with this pluginId again, because it was
		// overwritten by the mergeAnnotations method
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, mAnnotation);

		final boolean s_TransformToCNF =
				mServices.getPreferenceProvider(Activator.PLUGIN_ID).getBoolean(RcfgPreferenceInitializer.LABEL_CNF);

		mTransitionFormula = TransFormulaUtils.parallelComposition(mLogger, mServices, getSerialNumber(), mgdScript,
				null, s_TransformToCNF, xnfConversionTechnique, transFormulas);
		mTransitionFormulaWithBranchEncoders =
				TransFormulaUtils.parallelComposition(mLogger, mServices, getSerialNumber(), mgdScript, branchIndicator,
						s_TransformToCNF, xnfConversionTechnique, transFormulasWithBranchEncoders);
	}

	@Override
	public String getPrettyPrintedStatements() {
		if (mPrettyPrinted == null) {
			final StringBuilder sb = new StringBuilder();
			sb.append("BeginParallelComposition{");
			for (int i = 0; i < mCodeBlocks.size(); i++) {
				sb.append("ParallelCodeBlock" + i + ": ");
				sb.append(mCodeBlocks.get(i));
			}
			sb.append("}EndParallelComposition");
			mPrettyPrinted = sb.toString();
		}
		return mPrettyPrinted;
	}

	public Map<TermVariable, CodeBlock> getBranchIndicator2CodeBlock() {
		return mBranchIndicator2CodeBlock;
	}

	@Override
	public void setTransitionFormula(final UnmodifiableTransFormula transFormula) {
		throw new UnsupportedOperationException("transition formula is computed in constructor");
	}

	@Override
	public String toString() {
		return getPrettyPrintedStatements();
	}

	@Visualizable
	public List<CodeBlock> getCodeBlocks() {
		return Collections.unmodifiableList(mCodeBlocks);
	}
}
