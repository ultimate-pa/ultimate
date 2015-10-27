/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.AnnotatingRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.BaseRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpretationRcfgObserver extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final RCFGLoopDetector mLoopDetector;

	public AbstractInterpretationRcfgObserver(IUltimateServiceProvider services, RCFGLoopDetector loopDetector) {
		mServices = services;
		mLoopDetector = loopDetector;
	}

	@Override
	public boolean process(IElement elem) throws Throwable {
		// TODO: Library mode or main method mode? Currently, we only have main
		// method mode

		if (!(elem instanceof RootNode)) {
			throw new IllegalArgumentException("You cannot use this observer for " + elem.getClass().getSimpleName());
		}
		final RootNode root = (RootNode) elem;

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final List<CodeBlock> initial = getInitialEdges(root);
		if (initial == null) {
			throw new IllegalArgumentException("Could not find initial edge");
		}

		final Boogie2SmtSymbolTable boogieVarTable = root.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable();

		final IAbstractDomain<?, CodeBlock, BoogieVar> domain = selectDomain();
		final AbstractInterpreter<CodeBlock, BoogieVar> interpreter = createAbstractInterpreter(domain, symbolTable,
		        boogieVarTable);
		interpreter.process(initial);
		return false;
	}

	private BoogieSymbolTable getSymbolTable(RootNode root) {
		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			return null;
		}
		return pa.getSymbolTable();
	}

	private IAbstractDomain<?, CodeBlock, BoogieVar> selectDomain() {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final String selectedDomain = ups.getString(AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACT_DOMAIN);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(mServices);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(mServices);
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
		        + AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}

	private List<CodeBlock> getInitialEdges(RootNode root) {
		for (final RCFGEdge initialEdge : root.getOutgoingEdges()) {
			final ProgramPoint initialNode = (ProgramPoint) initialEdge.getTarget();
			if (initialNode.getProcedure().equals("ULTIMATE.start")) {
				List<RCFGEdge> edges = initialNode.getOutgoingEdges();
				List<CodeBlock> codeblocks = new ArrayList<CodeBlock>(edges.size());
				for (RCFGEdge edge : edges) {
					codeblocks.add((CodeBlock) edge);
				}
				return codeblocks;
			}
		}
		return null;
	}

	private AbstractInterpreter<CodeBlock, BoogieVar> createAbstractInterpreter(
	        IAbstractDomain<?, CodeBlock, BoogieVar> domain, BoogieSymbolTable table,
	        Boogie2SmtSymbolTable boogieVarTable) {
		assert domain != null;
		assert table != null;
		assert boogieVarTable != null;

		ITransitionProvider<CodeBlock> transitionProvider = new RcfgTransitionProvider();
		BaseRcfgAbstractStateStorageProvider storage = new AnnotatingRcfgAbstractStateStorageProvider(
		        domain.getMergeOperator(), mServices);
		IVariableProvider<CodeBlock, BoogieVar> varProvider = new RcfgVariableProvider(table, boogieVarTable);
		ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector(mLoopDetector);
		IResultReporter<CodeBlock> reporter = new RcfgResultReporter(mServices, storage);
		return new AbstractInterpreter<CodeBlock, BoogieVar>(mServices, transitionProvider, storage, domain,
		        varProvider, loopDetector, reporter);
	}

}
