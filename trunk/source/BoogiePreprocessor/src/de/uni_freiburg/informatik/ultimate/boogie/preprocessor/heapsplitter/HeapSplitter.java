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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.BoogiePreprocessorBacktranslator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class HeapSplitter implements IUnmanagedObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;

	private final AddressStoreFactory mAsfac;

	public HeapSplitter(final BoogiePreprocessorBacktranslator translator, final ILogger logger) {
		mTranslator = translator;
		mAsfac = new AddressStoreFactory();
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
		final MayAlias ma = aliasAnalysis(root);
		final Map<AddressStore, String> repToArray = new HashMap<>();
		{
			final UnionFind<AddressStore> uf = ma.getAddressStores();
			int ctr = 0;
			for (final AddressStore rep : uf.getAllRepresentatives()) {
				final String array = "#memory_int" + ctr;
				ctr++;
				repToArray.put(rep, array);
			}
		}
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final Collection<String> newHeapVarIds = repToArray.values();
			final ArrayDeque<Declaration> newDecls = new ArrayDeque<>();
			final HeapArrayReplacer har = new HeapArrayReplacer(mAsfac, ma, repToArray);
			for (final Declaration d : unit.getDeclarations()) {
				final List<VariableDeclaration> newHeapVarDecls = isHeapVarDecls(newHeapVarIds, d);
				if (newHeapVarDecls == null) {
					newDecls.add(d);
				} else {
					newDecls.addAll(newHeapVarDecls);
				}
				if (d instanceof Procedure) {
					final Procedure p = (Procedure) d;
					if (p.getBody() != null) {
						final MayAlias mas1 = processBody(p.getBody());
						final MayAlias mas2 = processBody2(p.getBody());
						final boolean same = mas1.equals(mas2);
						mas1.toString();
					}
				}
			}
			unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			return false;
		}
		return true;
	}

	public List<VariableDeclaration> isHeapVarDecls(final Collection<String> newHeapVarIds,
			final Declaration d) {
		if (d instanceof VariableDeclaration) {
			final VariableDeclaration varDecl = (VariableDeclaration) d;
			if (varDecl.getVariables().length == 1) {
				final VarList varList = varDecl.getVariables()[0];
				final String[] ids = varList.getIdentifiers();
				if (ids.length == 1) {
					if (ids[0].equals("#memory_int")) {
						return constructNewHeapVarDecls(varDecl, newHeapVarIds);
					}
				}
			}
		}
		return null;
	}

	public List<VariableDeclaration> constructNewHeapVarDecls(final VariableDeclaration varDecl,
			final Collection<String> newHeapVarIds) {
		final List<VariableDeclaration> newHeapVarDecls = new ArrayList<>();
		for (final String newHeapArray : newHeapVarIds) {
			newHeapVarDecls.add(constructNewHeapVarDecl(varDecl, newHeapArray));
		}
		return newHeapVarDecls;
	}

	public VariableDeclaration constructNewHeapVarDecl(final VariableDeclaration varDecl, final String newHeapArray) {
		assert varDecl.getVariables().length == 1;
		final VarList varList = varDecl.getVariables()[0];
		final VarList newVarList = new VarList(varList.getLoc(), new String[] { newHeapArray }, varList.getType(),
				varList.getWhereClause());
		ModelUtils.copyAnnotations(varList, newVarList);
		final VarList[] variables = new VarList[] { newVarList };
		final VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLoc(), varDecl.getAttributes(),
				variables);
		ModelUtils.copyAnnotations(varDecl, newVarDecl);
		return newVarDecl;
	}

	private MayAlias aliasAnalysis(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			for (final Declaration d : unit.getDeclarations()) {
				if (d instanceof Procedure) {
					final Procedure p = (Procedure) d;
					if (p.getBody() != null) {
						final MayAlias mas2 = processBody2(p.getBody());
						return mas2;
					}
				}
			}
		}
		throw new AssertionError("Analysis failed");
	}

	private MayAlias processBody(final Body body) {
		final Map<String, Integer> labelMapping = new HashMap<>();
		for (int i = 0; i < body.getBlock().length; i++) {
			if (body.getBlock()[i] instanceof Label) {
				final Label l = (Label) body.getBlock()[i];
				labelMapping.put(l.getName(), i);
			}
		}
		final MayAlias[] mas = new MayAlias[body.getBlock().length + 1];
		mas[0] = new MayAlias();
		final ArrayDeque<Integer> worklist = new ArrayDeque<>();
		worklist.add(0);
		while (!worklist.isEmpty()) {
			final Integer item = worklist.removeFirst();
			final MayAlias currentMa = mas[item];
			assert currentMa != null;
			final Statement st = body.getBlock()[item];
			if (st instanceof GotoStatement) {
				for (final String label : ((GotoStatement) st).getLabels()) {
					final int targetI = labelMapping.get(label);
					update(mas, worklist, targetI, currentMa);
				}
			} else if (st instanceof Label) {
				update(mas, worklist, item + 1, currentMa);
			} else if (st instanceof CallStatement) {
				final MayAlias succMa = processCallStatement(currentMa, (CallStatement) st);
				assert succMa != null;
				update(mas, worklist, item + 1, succMa);
			} else if (st instanceof AssignmentStatement) {
				final MayAlias succPei = processAssignmentStatement(currentMa, (AssignmentStatement) st);
				assert succPei != null;
				update(mas, worklist, item + 1, succPei);
			} else if (st instanceof AssumeStatement) {
				final MayAlias succPei = processAssumeStatement(currentMa, (AssumeStatement) st);
				assert succPei != null;
				update(mas, worklist, item + 1, succPei);
				assert succPei != null;
			} else if (st instanceof AssertStatement) {
				final MayAlias succPei = processAssertStatement(currentMa, (AssertStatement) st);
				assert succPei != null;
				update(mas, worklist, item + 1, succPei);
			} else if (st instanceof HavocStatement) {
				final MayAlias succPei = processHavocStatement(currentMa, (HavocStatement) st);
				assert succPei != null;
				update(mas, worklist, item + 1, succPei);
			} else if (st instanceof ReturnStatement) {
				final MayAlias succPei = currentMa;
				if (mas[item + 1] == null) {
					mas[item + 1] = succPei;
				} else {
					mas[item + 1] = mas[item + 1].join(succPei);
				}
			} else {
				throw new AssertionError("Unsuppored " + st);
			}
		}
		MayAlias res = mas[0];
		for (int i = 1; i < mas.length; i++) {
			if (mas[i] != null) {
				res = res.join(mas[i]);
			}
		}
		return res;
	}

	private MayAlias processBody2(final Body body) {
		MayAlias mas = new MayAlias();
		for (final Statement st : body.getBlock()) {
			if (st instanceof GotoStatement) {
				// do nothing
			} else if (st instanceof Label) {
				// do nothing
			} else if (st instanceof CallStatement) {
				mas = processCallStatement(mas, (CallStatement) st);
			} else if (st instanceof AssignmentStatement) {
				mas = processAssignmentStatement(mas, (AssignmentStatement) st);
			} else if (st instanceof AssumeStatement) {
				mas = processAssumeStatement(mas, (AssumeStatement) st);
			} else if (st instanceof AssertStatement) {
				mas = processAssertStatement(mas, (AssertStatement) st);
			} else if (st instanceof HavocStatement) {
				mas = processHavocStatement(mas, (HavocStatement) st);
			} else if (st instanceof ReturnStatement) {
				// do nothing
			} else {
				throw new AssertionError("Unsuppored " + st);
			}
		}
		return mas;
	}

	private MayAlias processHavocStatement(final MayAlias currentState, final HavocStatement st) {
		return currentState;
	}

	private MayAlias processAssertStatement(final MayAlias currentState, final AssertStatement st) {
		return currentState;
	}

	private MayAlias processAssumeStatement(final MayAlias currentState, final AssumeStatement st) {
		return currentState;
	}

	private MayAlias processAssignmentStatement(final MayAlias currentState, final AssignmentStatement st) {
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
					mAsfac.getPointerBase(vlhs.getIdentifier(), vlhs.getDeclarationInformation());
					final PointerBase pbLhs = mAsfac.getPointerBase(vlhs.getIdentifier(),
							vlhs.getDeclarationInformation());
					final PointerBase pbRhs = extractPointerBase(mAsfac, st.getRhs()[i]);
					variableUpdate.put(pbLhs, pbRhs);
				}
			}
		}
		if (variableUpdate.isEmpty()) {
			assert currentState != null;
			return currentState;
		} else {
			MayAlias res = currentState;
			for (final Entry<PointerBase, PointerBase> entry : variableUpdate.entrySet()) {
				if (isNullPointer(entry.getValue())) {
					res = res.addPointerBase(mAsfac, entry.getKey());
				} else {
					res = res.reportEquivalence(mAsfac, entry.getKey(), entry.getValue());
				}
			}
			assert res != null;
			return res;
		}

	}

	private Pair<PointerBase, PointerBase> extractPointerBaseUpdate(final Expression expression) {
		if (expression instanceof FunctionApplication) {
			final FunctionApplication fa = (FunctionApplication) expression;
			if (fa.getIdentifier().equals("~initToZeroAtPointerBaseAddress~$Pointer$.base")) {
				assert fa.getArguments().length == 3;
				assert isBaseArray(((IdentifierExpression) fa.getArguments()[0]).getIdentifier());
				final PointerBase index = extractPointerBase(mAsfac, fa.getArguments()[2]);
				final PointerBase value = mAsfac.getPointerBase(BigInteger.ZERO);
				return new Pair<>(index, value);
			}
		}
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
			final PointerBase index = extractPointerBase(mAsfac, indexExpr);
			final Expression valueExpr = ase.getValue();
			final PointerBase value = extractPointerBase(mAsfac, valueExpr);
			return new Pair<>(index, value);
		}
	}

	public static PointerBase extractPointerBase(final AddressStoreFactory mAsfac, final Expression expression) {
		if (expression instanceof IntegerLiteral) {
			final BigInteger value = new BigInteger(((IntegerLiteral) expression).getValue());
			return mAsfac.getPointerBase(value);
		} else if (expression instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expression;
			return mAsfac.getPointerBase(ie.getIdentifier(), ie.getDeclarationInformation());
		} else {
			throw new AssertionError("unknown PointerBase " + expression);
		}
	}

	private MayAlias processCallStatement(final MayAlias currentState, final CallStatement st) {
		if (st.getMethodName().equals("#Ultimate.allocInit")) {
			assert st.getArguments().length == 2;
			final Expression tmp = st.getArguments()[1];
			final PointerBase pb = extractPointerBase(mAsfac, tmp);
			return currentState.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals("#Ultimate.allocOnHeap")
				|| st.getMethodName().equals("#Ultimate.allocOnStack")) {
			assert st.getLhs().length == 2;
			final PointerBase pb = mAsfac.getPointerBase(st.getLhs()[0].getIdentifier(),
					st.getLhs()[0].getDeclarationInformation());
			return currentState.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals("write~$Pointer$")) {
			assert st.getArguments().length == 5;
			final Expression baseOfValueExpr = st.getArguments()[0];
			final Expression baseOfIndexExpr = st.getArguments()[2];
			final PointerBase baseOfValue = extractPointerBase(mAsfac, baseOfValueExpr);
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, baseOfIndexExpr);
			if (isNullPointer(baseOfValue)) {
				// do nothing
				return currentState;
			} else {
				final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
				return currentState.reportEquivalence(mAsfac, ms, baseOfValue);
			}
		} else if (st.getMethodName().equals("read~$Pointer$")) {
			assert st.getArguments().length == 3;
			assert st.getLhs().length == 2;
			final Expression baseOfIndexExpr = st.getArguments()[0];
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, baseOfIndexExpr);
			final PointerBase baseOfLhs = mAsfac.getPointerBase(st.getLhs()[0].getIdentifier(),
					st.getLhs()[0].getDeclarationInformation());
			final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
			return currentState.reportEquivalence(mAsfac, baseOfLhs, ms);
		} else if (st.getMethodName().equals("write~init~int")) {
		} else if (st.getMethodName().equals("write~init~$Pointer$")) {
		} else if (st.getMethodName().equals("write~int")) {
		} else if (st.getMethodName().equals("read~int")) {
		} else if (st.getMethodName().equals("ULTIMATE.dealloc")) {
		} else if (st.getMethodName().equals("read~unchecked~int")) {
		} else if (st.getMethodName().equals("write~unchecked~int")) {
		// TODO handle properly!
		} else if (st.getMethodName().equals("read~unchecked~$Pointer$")) {
		} else if (st.getMethodName().equals("write~unchecked~$Pointer$")) {
		} else {
			throw new AssertionError("unsupported method " + st.getMethodName());
		}
		return currentState;
	}

	private void update(final MayAlias[] states, final ArrayDeque<Integer> worklist, final int targetI,
			final MayAlias currentState) {
		assert (currentState != null);
		if (states[targetI] == null) {
			states[targetI] = currentState;
			worklist.add(targetI);
		} else if (!states[targetI].equals(currentState)) {
			states[targetI] = states[targetI].join(currentState);
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
