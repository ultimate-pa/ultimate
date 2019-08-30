/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.MultiTermResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Statements2TransFormula.TranslationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;

/**
 * Provides methods to add TransitionsFormulas to the edges of a recursive control flow graph.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TransFormulaAdder {

	// We use Boogie2SMT to translate boogie Statements to SMT formulas
	private final Boogie2SMT mBoogie2smt;
	private final boolean mSimplifyCodeBlocks;

	private final IUltimateServiceProvider mServices;

	public TransFormulaAdder(final Boogie2SMT boogie2smt, final IUltimateServiceProvider services) {
		mServices = services;
		mBoogie2smt = boogie2smt;
		mSimplifyCodeBlocks = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLIFY);
	}

	/**
	 * Add TransitionFormulas to an edge in the recursive control flow graph. If the edge is a CallEdge or ReturnEdge
	 * two formulas are added. One that represents the local variable assignments one that represents the global
	 * variable assignments. If the edge is an InternalEdge one TransitionFormula is added. This TransitionFormula
	 * represents the effect of all Assignment, Assume and Havoc Statements of this edge. If the edge is a GotoEdge or a
	 * SummaryEdge no TransitionFormula is added.
	 *
	 * @param cb
	 *            An IEdge that has to be a CallEdge, InternalEdge, ReturnEdge, GotoEdge or SummaryEdge.
	 */
	public void addTransitionFormulas(final CodeBlock cb, final String procId,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		List<Statement> statements;
		if (cb instanceof StatementSequence) {
			statements = ((StatementSequence) cb).getStatements();
		} else if (cb instanceof Summary) {
			statements = Collections.singletonList(((Summary) cb).getCallStatement());
		} else if (cb instanceof ForkThreadCurrent) {
			final ForkThreadCurrent fork = (ForkThreadCurrent) cb;
			statements = Collections.singletonList(fork.getForkStatement());
			final ForkSmtArguments fsa = constructForkSmtArguments(fork.getForkStatement(), mBoogie2smt);
			fork.setForkSmtArguments(fsa);
		} else if (cb instanceof JoinThreadCurrent) {
			final JoinThreadCurrent join = (JoinThreadCurrent) cb;
			statements = Collections.singletonList(join.getJoinStatement());
			final JoinSmtArguments jsa = constructJoinSmtArguments(join.getJoinStatement(), mBoogie2smt);
			join.setJoinSmtArguments(jsa);
		} else if (cb instanceof GotoEdge) {
			statements = Collections.emptyList();
		} else {
			throw new AssertionError(
					"Cannot add transition formula to CodeBlock of type " + cb.getClass().getSimpleName());
		}

		TranslationResult tlres = null;
		try {
			tlres = mBoogie2smt.getStatements2TransFormula().statementSequence(mSimplifyCodeBlocks,
					simplificationTechnique, procId, statements);
		} catch (final SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				reportUnsupportedSyntax(cb, e.getMessage());
			}
			throw e;
		}
		if (!tlres.getOverapproximations().isEmpty()) {
			new Overapprox(tlres.getOverapproximations()).annotate(cb);
		}
		cb.setTransitionFormula(tlres.getTransFormula());
	}

	private static ForkSmtArguments constructForkSmtArguments(final ForkStatement st, final Boogie2SMT boogie2smt) {
		final IIdentifierTranslator[] identifierTranslators = new IIdentifierTranslator[] {
				boogie2smt.new LocalVarAndGlobalVarTranslator(), boogie2smt.createConstOnlyIdentifierTranslator() };
		final MultiTermResult threadId =
				boogie2smt.getExpression2Term().translateToTerms(identifierTranslators, st.getThreadID());
		if (!threadId.getAuxiliaryVars().isEmpty()) {
			throw new UnsupportedOperationException("auxvars not yet supported");
		}
		if (!threadId.getOverappoximations().isEmpty()) {
			throw new UnsupportedOperationException("overapproximations not yet supported");
		}
		final MultiTermResult procedureArguments =
				boogie2smt.getExpression2Term().translateToTerms(identifierTranslators, st.getArguments());
		if (!procedureArguments.getAuxiliaryVars().isEmpty()) {
			throw new UnsupportedOperationException("auxvars not yet supported");
		}
		if (!procedureArguments.getOverappoximations().isEmpty()) {
			throw new UnsupportedOperationException("overapproximations not yet supported");
		}
		return new ForkSmtArguments(threadId, procedureArguments);
	}

	private static JoinSmtArguments constructJoinSmtArguments(final JoinStatement st, final Boogie2SMT boogie2smt) {
		final IIdentifierTranslator[] identifierTranslators = new IIdentifierTranslator[] {
				boogie2smt.new LocalVarAndGlobalVarTranslator(), boogie2smt.createConstOnlyIdentifierTranslator() };
		final MultiTermResult threadId =
				boogie2smt.getExpression2Term().translateToTerms(identifierTranslators, st.getThreadID());
		if (!threadId.getAuxiliaryVars().isEmpty()) {
			throw new UnsupportedOperationException("auxvars not yet supported");
		}
		if (!threadId.getOverappoximations().isEmpty()) {
			throw new UnsupportedOperationException("overapproximations not yet supported");
		}
		final List<IProgramVar> assignmentLhs = new ArrayList<>();
		for (final VariableLHS lhs : st.getLhs()) {
			final IProgramVar pv = boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(lhs.getIdentifier(),
					lhs.getDeclarationInformation(), false);
			assignmentLhs.add(pv);

		}
		return new JoinSmtArguments(threadId, assignmentLhs);
	}

	void reportUnsupportedSyntax(final CodeBlock cb, final String longDescription) {
		final ILocation loc = ILocation.getAnnotation(cb);
		final SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME, loc, longDescription);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}
}
