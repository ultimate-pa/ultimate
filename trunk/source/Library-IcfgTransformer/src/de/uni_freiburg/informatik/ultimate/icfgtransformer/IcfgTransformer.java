/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.IIcfg;

/**
 * Example IcfgTransformer that applies the {@link ExampleLoopAccelerationTransformulaTransformer}, i.e., replaces all
 * transformulas of an {@link IIcfg} with a new instance.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformer {
	
	private final ILogger mLogger;
	private final IIcfg<?> mResultIcfg;
	private final ManagedScript mManagedScript;
	private final Map<IcfgLocation, IcfgLocation> mOldLoc2NewLoc;
	
	public IcfgTransformer(final ILogger logger, final IIcfg<?> originalIcfg) {
		mLogger = logger;
		mManagedScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mOldLoc2NewLoc = new HashMap<>();
		mResultIcfg = transform(originalIcfg);
	}
	
	private IIcfg<?> transform(final IIcfg<? extends IcfgLocation> originalIcfg) {
		final IIcfg<?> resultIcfg = createEmptyIcfg(originalIcfg);
		
		final IIcfgSymbolTable origSymbolTable = originalIcfg.getSymboltable();
		final ReplacementVarFactory fac = new ReplacementVarFactory(resultIcfg.getCfgSmtToolkit(), false);
		
		final Set<? extends IcfgLocation> init = originalIcfg.getInitialNodes();
		final Deque<IcfgLocation> open = new ArrayDeque<>(init);
		final Set<IcfgLocation> closed = new HashSet<>();
		
		while (!open.isEmpty()) {
			final IcfgLocation current = open.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			
			final IcfgLocation newSource = createNewLocation(originalIcfg, resultIcfg, current);
			for (final IcfgEdge currentEdge : current.getOutgoingEdges()) {
				final IcfgLocation newTarget = createNewLocation(originalIcfg, resultIcfg, current);
				final IcfgEdge newEdge;
				if (currentEdge instanceof IInternalAction) {
					newEdge = createNewInternalAction(newSource, newTarget, (IInternalAction) currentEdge,
							origSymbolTable, fac);
				} else if (currentEdge instanceof ICallAction) {
					newEdge =
							createNewCallAction(newSource, newTarget, (ICallAction) currentEdge, origSymbolTable, fac);
				} else if (currentEdge instanceof IReturnAction) {
					newEdge = createNewReturnAction(newSource, newTarget, (IReturnAction) currentEdge, origSymbolTable,
							fac);
				} else {
					throw new IllegalArgumentException("Unknown edge type " + currentEdge.getClass().getSimpleName());
				}
				newSource.addOutgoing(newEdge);
				newTarget.addIncoming(newEdge);
			}
		}
		
		return resultIcfg;
	}
	
	private IcfgEdge createNewReturnAction(final IcfgLocation source, final IcfgLocation target,
			final IReturnAction edge, final IIcfgSymbolTable origSymbolTable, final ReplacementVarFactory fac) {
		final UnmodifiableTransFormula retAssign =
				getFreshTransFormula(origSymbolTable, fac, edge.getAssignmentOfReturn());
		final UnmodifiableTransFormula localVarAssign =
				getFreshTransFormula(origSymbolTable, fac, edge.getLocalVarsAssignmentOfCall());
		return new IcfgReturnAction(source, target, null, retAssign, localVarAssign);
	}
	
	private IcfgEdge createNewCallAction(final IcfgLocation source, final IcfgLocation target, final ICallAction edge,
			final IIcfgSymbolTable origSymbolTable, final ReplacementVarFactory fac) {
		final UnmodifiableTransFormula unmodTf =
				getFreshTransFormula(origSymbolTable, fac, edge.getLocalVarsAssignment());
		return new IcfgCallAction(source, target, null, unmodTf);
	}
	
	private IcfgEdge createNewInternalAction(final IcfgLocation source, final IcfgLocation target,
			final IInternalAction edge, final IIcfgSymbolTable origSymbolTable, final ReplacementVarFactory fac) {
		final UnmodifiableTransFormula unmodTf = getFreshTransFormula(origSymbolTable, fac, edge.getTransformula());
		return new IcfgInternalAction(source, target, null, unmodTf);
	}
	
	private UnmodifiableTransFormula getFreshTransFormula(final IIcfgSymbolTable origSymbolTable,
			final ReplacementVarFactory fac, final TransFormula tf) {
		final ExampleLoopAccelerationTransformulaTransformer transformer =
				new ExampleLoopAccelerationTransformulaTransformer(mLogger, mManagedScript, origSymbolTable, fac, tf);
		final TransFormula newTransformula = transformer.getTransformationResult();
		// TODO: How to create unmodifiable transformula from transformula?
		final UnmodifiableTransFormula unmodTf = null;
		return unmodTf;
	}
	
	private IcfgLocation createNewLocation(final IIcfg<? extends IcfgLocation> originalIcfg, final IIcfg<?> resultIcfg,
			final IcfgLocation current) {
		final IcfgLocation alreadyCreated = mOldLoc2NewLoc.get(current);
		if (alreadyCreated != null) {
			return alreadyCreated;
		}
		
		final String proc = current.getProcedure();
		final IcfgLocation fresh = new IcfgLocation(current.getDebugIdentifier(), proc);
		
		// TODO: Insert in appropriate maps of resultIcfg
		// final boolean isErrorLoc = originalIcfg.getProcedureErrorNodes().get(proc).contains(current);
		
		// cache created IcfgLocation
		mOldLoc2NewLoc.put(current, fresh);
		
		return fresh;
	}
	
	private IIcfg<?> createEmptyIcfg(final IIcfg<?> originalIcfg) {
		// TODO: Build BaseIcfg implementation and create a new, empty IIcfg instance.
		return originalIcfg;
	}
	
	public IIcfg<?> getResult() {
		return mResultIcfg;
	}
	
}
