/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Class that handles expanding of structs into normal variables.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.BoogiePreprocessorBacktranslator;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter.PointerEquivalenceInfo.PointerBase;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter.PointerEquivalenceInfo.PointerBaseIntLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter.PointerEquivalenceInfo.PointerBaseVariable;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter.PointerEquivalenceInfo.PointerBasesOnHeap;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class HeapSplitter implements IUnmanagedObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;

	public HeapSplitter(final BoogiePreprocessorBacktranslator translator, final ILogger logger) {
		mTranslator = translator;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return true;
	}

	/**
	 * Process the boogie code.
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			for (final Declaration d : unit.getDeclarations()) {
				if (d instanceof Procedure) {
					final Procedure p = (Procedure) d;
					if (p.getBody() != null) {
						processBody(p.getBody());
					}
				}
			}
		}
		return true;
	}

	private void processBody(final Body body) {
		final Map<String, Integer> labelMapping = new HashMap<>();
		for (int i = 0; i < body.getBlock().length; i++) {
			if (body.getBlock()[i] instanceof Label) {
				final Label l = (Label) body.getBlock()[i];
				labelMapping.put(l.getName(), i);
			}
		}
		final PointerEquivalenceInfo[] peis = new PointerEquivalenceInfo[body.getBlock().length + 1];
		peis[0] = new PointerEquivalenceInfo(new HashRelation<>(), new UnionFind<>());
		final ArrayDeque<Integer> worklist = new ArrayDeque<>();
		worklist.add(0);
		while (!worklist.isEmpty()) {
			final Integer item = worklist.removeFirst();
			final PointerEquivalenceInfo currentPei = peis[item];
			assert currentPei != null;
			final Statement st = body.getBlock()[item];
			if (st instanceof GotoStatement) {
				for (final String label : ((GotoStatement) st).getLabels()) {
					final int targetI = labelMapping.get(label);
					update(peis, worklist, targetI, currentPei);
				}
			} else if (st instanceof Label) {
				update(peis, worklist, item + 1, currentPei);
			} else if (st instanceof CallStatement) {
				final PointerEquivalenceInfo succPei = processCallStatement(currentPei, (CallStatement) st);
				assert succPei != null;
				update(peis, worklist, item + 1, succPei);
			} else if (st instanceof AssignmentStatement) {
				final PointerEquivalenceInfo succPei = processAssignmentStatement(currentPei, (AssignmentStatement) st);
				assert succPei != null;
				update(peis, worklist, item + 1, succPei);
			} else if (st instanceof AssumeStatement) {
				final PointerEquivalenceInfo succPei = processAssumeStatement(currentPei, (AssumeStatement) st);
				assert succPei != null;
				update(peis, worklist, item + 1, succPei);
				assert succPei != null;
			} else if (st instanceof AssertStatement) {
				final PointerEquivalenceInfo succPei = processAssertStatement(currentPei, (AssertStatement) st);
				assert succPei != null;
				update(peis, worklist, item + 1, succPei);
			} else if (st instanceof HavocStatement) {
				final PointerEquivalenceInfo succPei = processHavocStatement(currentPei, (HavocStatement) st);
				assert succPei != null;
				update(peis, worklist, item + 1, succPei);
			} else if (st instanceof ReturnStatement) {
				final PointerEquivalenceInfo succPei = currentPei;
				if (peis[item + 1] == null) {
					peis[item + 1] = succPei;
				} else {
					peis[item + 1] = peis[item + 1].union(succPei);
				}
			} else {
				throw new AssertionError("Unsuppored " + st);
			}
		}
		PointerEquivalenceInfo res = peis[0];
		for (int i = 1; i < peis.length; i++) {
			if (peis[i] != null) {
				res = res.union(peis[i]);
			}
		}
		peis.toString();
	}

	private PointerEquivalenceInfo processHavocStatement(final PointerEquivalenceInfo currentState,
			final HavocStatement st) {
		return currentState;
	}

	private PointerEquivalenceInfo processAssertStatement(final PointerEquivalenceInfo currentState,
			final AssertStatement st) {
		return currentState;
	}

	private PointerEquivalenceInfo processAssumeStatement(final PointerEquivalenceInfo currentState,
			final AssumeStatement st) {
		return currentState;
	}

	private PointerEquivalenceInfo processAssignmentStatement(final PointerEquivalenceInfo currentState,
			final AssignmentStatement st) {
		final Map<PointerBase, PointerBase> variableUpdate = new HashMap<>();
		final Map<PointerBase, PointerBase> pointerArrayUpdate = new HashMap<>();
		final LeftHandSide[] lhs = st.getLhs();
		for (int i = 0; i < lhs.length; i++) {
			if (lhs[i] instanceof VariableLHS) {
				final VariableLHS vlhs = (VariableLHS) lhs[i];
				if (isBaseArray(vlhs.getIdentifier())) {
					final Pair<PointerBase, PointerBase> pair = extractPointerBaseUpdate(st.getRhs()[i]);
					pointerArrayUpdate.put(pair.getFirst(), pair.getSecond());
					if (!isNullPointer(pair.getSecond())) {
						throw new AssertionError("we have to do something");
					}
				} else if (isPointer(vlhs.getIdentifier())) {
					final PointerBase pbLhs = new PointerBaseVariable(vlhs.getIdentifier());
					final PointerBase pbRhs = extractPointerBase(st.getRhs()[i]);
					variableUpdate.put(pbLhs, pbRhs);
				}
			}
		}
		if (variableUpdate.isEmpty()) {
			assert currentState != null;
			return currentState;
		} else {
			PointerEquivalenceInfo res = currentState;
			for (final Entry<PointerBase, PointerBase> entry : variableUpdate.entrySet()) {
				if (isNullPointer(entry.getValue())) {
					res = res.announce(entry.getKey());
				} else {
					res = res.assignment(entry.getKey(), entry.getValue());
				}
			}
			assert res != null;
			return res;
		}

	}

	private Pair<PointerBase, PointerBase> extractPointerBaseUpdate(final Expression expression) {
		if (!(expression instanceof ArrayStoreExpression)) {
			throw new AssertionError("No array!");
		} else {
			final ArrayStoreExpression ase = (ArrayStoreExpression) expression;
			final Expression arr = ase.getArray();
			if (!(arr instanceof IdentifierExpression)) {
				throw new AssertionError("Not pointerBase array!");
			}
			final IdentifierExpression ie = (IdentifierExpression) arr;
			if (!isBaseArray(ie.getIdentifier())) {
				throw new AssertionError("Not pointerBase array!");
			}
			if (ase.getIndices().length != 2) {
				throw new AssertionError("Not pointerBase array!");
			}
			final Expression indexExpr = ase.getIndices()[0];
			final PointerBase index = extractPointerBase(indexExpr);
			final Expression valueExpr = ase.getValue();
			final PointerBase value = extractPointerBase(valueExpr);
			return new Pair<>(index, value);
		}
	}

	private PointerBase extractPointerBase(final Expression expression) {
		if (expression instanceof IntegerLiteral) {
			return new PointerBaseIntLiteral(new BigInteger(((IntegerLiteral) expression).getValue()));
		} else if (expression instanceof IdentifierExpression) {
			return new PointerBaseVariable(((IdentifierExpression) expression).getIdentifier());
//		} else if (expression instanceof ArrayStoreExpression) {
//			expression.toString();
		} else {
			throw new AssertionError("unknown PointerBase " + expression);
		}
	}

	private PointerEquivalenceInfo processCallStatement(final PointerEquivalenceInfo currentState,
			final CallStatement st) {
		if (st.getMethodName().equals("#Ultimate.allocInit")) {
			assert st.getArguments().length == 2;
			final Expression tmp = st.getArguments()[1];
			if (tmp instanceof IntegerLiteral) {
				final IntegerLiteral il = (IntegerLiteral) tmp;
				final PointerBase pb = new PointerBaseVariable(il.getValue());
				return currentState.addPointerBase(pb);
			} else {
				throw new AssertionError("unsupported expression");
			}
		} else if (st.getMethodName().equals("#Ultimate.allocOnHeap")
				|| st.getMethodName().equals("#Ultimate.allocOnStack")) {
			assert st.getLhs().length == 2;
			final PointerBase pb = new PointerBaseVariable(st.getLhs()[0].getIdentifier());
			return currentState.addPointerBase(pb);
		} else if (st.getMethodName().equals("write~$Pointer$")) {
			assert st.getArguments().length == 5;
			final Expression baseOfValueExpr = st.getArguments()[0];
			final Expression baseOfIndexExpr = st.getArguments()[2];
			final PointerBase baseOfValue = extractPointerBase(baseOfValueExpr);
			final PointerBase baseOfIndex = extractPointerBase(baseOfIndexExpr);
			if (isNullPointer(baseOfValue)) {
				// do nothing
				return currentState;
			} else {
				return currentState.addEquivalence(new PointerBasesOnHeap(baseOfIndex), baseOfValue);
			}
		} else if (st.getMethodName().equals("read~$Pointer$")) {
			assert st.getArguments().length == 3;
			assert st.getLhs().length == 2;
			final Expression baseOfIndexExpr = st.getArguments()[0];
			final PointerBase baseOfIndex = extractPointerBase(baseOfIndexExpr);
			final PointerBase baseOfLhs = new PointerBaseVariable(st.getLhs()[0].getIdentifier());
			return currentState.assignment(baseOfLhs, new PointerBasesOnHeap(baseOfIndex));
		} else if (st.getMethodName().equals("write~init~int")) {
		} else if (st.getMethodName().equals("write~init~$Pointer$")) {
		} else if (st.getMethodName().equals("write~int")) {
		} else if (st.getMethodName().equals("read~int")) {
		} else if (st.getMethodName().equals("ULTIMATE.dealloc")) {
		} else {
			throw new AssertionError("unsupported method " + st.getMethodName());
		}
		return currentState;
	}

	private void update(final PointerEquivalenceInfo[] states, final ArrayDeque<Integer> worklist, final int targetI,
			final PointerEquivalenceInfo currentState) {
		assert (currentState != null);
		if (states[targetI] == null) {
			states[targetI] = currentState;
			worklist.add(targetI);
		} else if (!states[targetI].equals(currentState)) {
			states[targetI] = states[targetI].union(currentState);
			worklist.add(targetI);
		} else {
			// no change, no need to add something to worklist
		}

	}

	private boolean isPointer(final String identifier) {
		return identifier.endsWith(".base");
	}

	private boolean isNullPointer(final PointerBase pbRhs) {
		return (pbRhs.toString().equals("0"));
	}

	private boolean isBaseArray(final String identifier) {
		return identifier.equals("#memory_$Pointer$.base");
	}

}
