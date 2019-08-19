/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;

/**
 * Factory for the construction of CodeBlocks. Every CodeBlock has to be constructed via this factory, because every
 * CodeBlock need a unique serial number. Every control flow graph has to provide one CodeBlockFactory
 *
 * @author Matthias Heizmann
 *
 */
public class CodeBlockFactory implements IStorable {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final CfgSmtToolkit mMgvManager;
	private final SerialProvider mSerialProvider;

	public CodeBlockFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final CfgSmtToolkit mgvManager, final IIcfgSymbolTable symbolTable, final SerialProvider serialProvider) {
		super();
		mSerialProvider = serialProvider;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMgdScript = mgdScript;
		mMgvManager = mgvManager;
	}

	public Call constructCall(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final CallStatement call) {
		return new Call(makeFreshSerial(), source, target, call, mLogger);
	}

	public ForkThreadCurrent constructForkCurrentThread(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final ForkStatement fork, final boolean forkedProcedureHasImplementation) {
		return new ForkThreadCurrent(makeFreshSerial(), source, target, fork, forkedProcedureHasImplementation,
				mLogger);
	}

	public JoinThreadCurrent constructJoinCurrentThread(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final JoinStatement join) {
		return new JoinThreadCurrent(makeFreshSerial(), source, target, join, mLogger);
	}

	public ForkThreadOther constructForkOtherThread(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final ForkStatement fork, final ForkThreadCurrent forkCurrentThread) {
		return new ForkThreadOther(makeFreshSerial(), source, target, fork, forkCurrentThread, mLogger);
	}

	public JoinThreadOther constructJoinOtherThread(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final JoinStatement join, final JoinThreadCurrent joinCurrentThread) {
		return new JoinThreadOther(makeFreshSerial(), source, target, join, joinCurrentThread, mLogger);
	}

	public GotoEdge constructGotoEdge(final BoogieIcfgLocation source, final BoogieIcfgLocation target) {
		return new GotoEdge(makeFreshSerial(), source, target, mLogger);
	}

	public ParallelComposition constructParallelComposition(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final List<CodeBlock> codeBlocks,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		return new ParallelComposition(makeFreshSerial(), source, target, mMgdScript, mServices, codeBlocks,
				xnfConversionTechnique);
	}

	public Return constructReturn(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final Call correspondingCall) {
		return new Return(makeFreshSerial(), source, target, correspondingCall, mLogger);
	}

	public SequentialComposition constructSequentialComposition(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final boolean simplify, final boolean extPqe,
			final List<CodeBlock> codeBlocks, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		return new SequentialComposition(makeFreshSerial(), source, target, mMgvManager, simplify, extPqe, mServices,
				codeBlocks, xnfConversionTechnique, simplificationTechnique);
	}

	public StatementSequence constructStatementSequence(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final Statement st) {
		return new StatementSequence(makeFreshSerial(), source, target, st, mLogger);
	}

	public StatementSequence constructStatementSequence(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final Statement st, final Origin origin) {
		return new StatementSequence(makeFreshSerial(), source, target, st, origin, mLogger);
	}

	public StatementSequence constructStatementSequence(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final List<Statement> stmts, final Origin origin) {
		return new StatementSequence(makeFreshSerial(), source, target, stmts, origin, mLogger);
	}

	public Summary constructSummary(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final CallStatement st, final boolean calledProcedureHasImplementation) {
		return new Summary(makeFreshSerial(), source, target, st, calledProcedureHasImplementation, mLogger);
	}

	private int makeFreshSerial() {
		return mSerialProvider.getFreshSerial();
	}

	public CodeBlock copyCodeBlock(final CodeBlock codeBlock, final BoogieIcfgLocation source,
			final BoogieIcfgLocation target) {
		if (codeBlock instanceof Call) {
			final Call copy = constructCall(source, target, ((Call) codeBlock).getCallStatement());
			copy.setTransitionFormula(codeBlock.getTransformula());
			return copy;
		} else if (codeBlock instanceof Return) {
			// FIXME: The return keeps its reference to the old call and thus to a possibly old Icfg
			final Return copy = constructReturn(source, target, ((Return) codeBlock).getCorrespondingCall());
			copy.setTransitionFormula(codeBlock.getTransformula());
			return copy;
		} else if (codeBlock instanceof StatementSequence) {
			final List<Statement> statements = ((StatementSequence) codeBlock).getStatements();
			final Origin origin = ((StatementSequence) codeBlock).getOrigin();
			final StatementSequence copy = this.constructStatementSequence(source, target, statements, origin);
			copy.setTransitionFormula(codeBlock.getTransformula());
			return copy;
		} else if (codeBlock instanceof Summary) {
			final CallStatement callStatement = ((Summary) codeBlock).getCallStatement();
			final boolean calledProcedureHasImplementation = ((Summary) codeBlock).calledProcedureHasImplementation();
			final Summary copy = constructSummary(source, target, callStatement, calledProcedureHasImplementation);
			copy.setTransitionFormula(codeBlock.getTransformula());
			return copy;
		} else if (codeBlock instanceof GotoEdge) {
			return constructGotoEdge(source, target);
		} else {
			throw new UnsupportedOperationException(
					"unsupported kind of CodeBlock: " + codeBlock.getClass().getSimpleName());
		}
	}

	@Override
	public void destroy() {
		// nothing to destroy
	}

	public static CodeBlockFactory getFactory(final IToolchainStorage storage) {
		return (CodeBlockFactory) storage.getStorable(CodeBlockFactory.class.getName());
	}

	public void storeFactory(final IToolchainStorage storage) {
		storage.putStorable(CodeBlockFactory.class.getName(), this);
	}

}
