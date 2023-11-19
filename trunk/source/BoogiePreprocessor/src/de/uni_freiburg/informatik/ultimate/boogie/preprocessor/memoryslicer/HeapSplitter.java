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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
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

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class HeapSplitter implements IUnmanagedObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;

	private final AddressStoreFactory mAsfac;
	private final ILogger mLogger;

	public HeapSplitter(final BoogiePreprocessorBacktranslator translator, final ILogger logger) {
		mTranslator = translator;
		mAsfac = new AddressStoreFactory();
		mLogger = logger;
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

			final AliasAnalysis aa = new AliasAnalysis(mAsfac);
			final MayAlias ma = aa.aliasAnalysis(unit);
			final Map<AddressStore, Integer> repToArray = new HashMap<>();
			{
				final UnionFind<AddressStore> uf = ma.getAddressStores();
				int ctr = 0;
				final Set<AddressStore> representativesOfAccesses = new HashSet<>();
				for (final PointerBase tmp : aa.getAccessAddresses()) {
					final AddressStore rep = uf.find(tmp);
					assert rep != null;
					representativesOfAccesses.add(rep);
				}
				for (final AddressStore rep : representativesOfAccesses) {
					repToArray.put(rep, ctr);
					ctr++;
				}
			}
			final Collection<Integer> newHeapSliceIds = repToArray.values();
			final Collection<String> memorySliceSuffixes = new ArrayList<>();
			for (final Integer memorySliceId : repToArray.values()) {
				final String memorySliceSuffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceId);
				memorySliceSuffixes.add(memorySliceSuffix);
			}

			final ArrayDeque<Declaration> newDecls = new ArrayDeque<>();
			final HeapArrayReplacer har = new HeapArrayReplacer(mAsfac, ma, repToArray);
			for (final Declaration d : unit.getDeclarations()) {
				final List<String> memoryArrays = Arrays.asList(new String[] { MemorySliceUtils.MEMORY_INT,
						MemorySliceUtils.MEMORY_POINTER_BASE, MemorySliceUtils.MEMORY_POINTER_OFFSET });
				final List<VariableDeclaration> newHeapVarDecls = duplicateMemoryArrayVarDecl(memoryArrays,
						memorySliceSuffixes, d);
				if (newHeapVarDecls != null) {
					newDecls.addAll(newHeapVarDecls);
				} else if (d instanceof Procedure) {
					final Procedure proc = (Procedure) d;
					if (toList(MemorySliceUtils.READ_INT, MemorySliceUtils.READ_UNCHECKED_INT,
							MemorySliceUtils.WRITE_INT, MemorySliceUtils.WRITE_INIT_INT, MemorySliceUtils.READ_POINTER,
							MemorySliceUtils.WRITE_POINTER).contains(proc.getIdentifier())) {
						final List<Procedure> duplicates = duplicateProcedure(memoryArrays, memorySliceSuffixes,
								(Procedure) d);
						newDecls.addAll(duplicates);
//					} else if (proc.getIdentifier().equals(WRITE_POINTER)) {
//						final Procedure result = reviseWritePointer(newHeapSliceIds, proc);
//						newDecls.add(result);
//					} else if (proc.getBody() == null) {
//						// procedures without implementation
//						newDecls.add(d);
					} else {
						final Declaration newDecl = har.processDeclaration(proc);
						newDecls.add(newDecl);
					}
				} else {
					newDecls.add(d);
				}
//				if (d instanceof Procedure) {
//					final Procedure p = (Procedure) d;
//					if (p.getBody() != null) {
//						final MayAlias mas1 = processBody(p.getBody());
//						final MayAlias mas2 = processBody2(p.getBody());
//						final boolean same = mas1.equals(mas2);
//						mas1.toString();
//					}
//				}
			}
			final String logMessage = constructLogMessage(har.getAccessCounter(), har.getSliceAccessCounter());
			mLogger.info(logMessage);
			unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			return false;
		}
		return true;
	}

	private Procedure reviseWritePointer(final Collection<Integer> heapSliceIds, final Procedure proc) {
		// assuming that we have two specifications, first ensures, then modifies
		assert proc.getSpecification().length == 2;
		final EnsuresSpecification es = (EnsuresSpecification) proc.getSpecification()[0];
		final ModifiesSpecification ms = (ModifiesSpecification) proc.getSpecification()[1];
		final List<Specification> newSpecs = new ArrayList<>();
		for (final Integer heapSliceId : heapSliceIds) {
			final String heapSliceSuffix = MemorySliceUtils.constructMemorySliceSuffix(heapSliceId);
			final IdentifierReplacer ir = new IdentifierReplacer(
					Collections.singletonMap(MemorySliceUtils.MEMORY_INT, MemorySliceUtils.MEMORY_INT + heapSliceSuffix));
			final EnsuresSpecification newEs = (EnsuresSpecification) ir.processSpecification(es);
			newSpecs.add(newEs);
		}
		final ModifiesSpecification newMs = reviseModifiesSpec(heapSliceIds, ms, MemorySliceUtils.MEMORY_INT);
		newSpecs.add(newMs);
		final Procedure result = new Procedure(proc.getLoc(), proc.getAttributes(), proc.getIdentifier(),
				proc.getTypeParams(), proc.getInParams(), proc.getOutParams(),
				newSpecs.toArray(new Specification[newSpecs.size()]), null);
		ModelUtils.copyAnnotations(proc, result);
		return result;
	}

	public static ModifiesSpecification reviseModifiesSpec(final Collection<Integer> heapSliceIds,
			final ModifiesSpecification oldMs, final String... memoryInt) {
		final VariableLHS[] oldIds = oldMs.getIdentifiers();
		final List<VariableLHS> newIds = new ArrayList<>();
		for (final VariableLHS oldId : oldIds) {
			if (Arrays.asList(memoryInt).contains(oldId.getIdentifier())) {
				for (final Integer heapSliceId : heapSliceIds) {
					final String heapSliceSuffix = MemorySliceUtils.constructMemorySliceSuffix(heapSliceId);
					final VariableLHS vlhs = new VariableLHS(oldId.getLoc(), oldId.getType(),
							oldId.getIdentifier() + heapSliceSuffix, oldId.getDeclarationInformation());
					ModelUtils.copyAnnotations(oldId, vlhs);
					newIds.add(vlhs);
				}
			} else {
				newIds.add(oldId);
			}
		}
		final ModifiesSpecification result = new ModifiesSpecification(oldMs.getLoc(), oldMs.isFree(),
				newIds.toArray(new VariableLHS[newIds.size()]));
		ModelUtils.copyAnnotations(oldMs, result);
		return result;
	}

	private static List<String> toList(final String... identifiers) {
		return Arrays.asList(identifiers);
	}

	private String constructLogMessage(final int accessCounter, final int[] sliceAccessCounter) {
		return String.format("Split %s memory accesses to %s slices as follows %s", accessCounter,
				sliceAccessCounter.length, Arrays.toString(sliceAccessCounter));
	}

//	private String constructLogMessage()

	public boolean isProcedure(final Declaration d, final String... identifiers) {
		if (d instanceof Procedure) {
			final Procedure proc = (Procedure) d;
			if (Arrays.asList(identifiers).contains(proc.getIdentifier())) {
				return true;
			}
		}
		return false;
	}

	private static List<Procedure> duplicateProcedure(final List<String> memoryArrays,
			final Collection<String> memorySliceSuffixes, final Procedure p) {
		final List<Procedure> res = new ArrayList<>(memorySliceSuffixes.size());
		for (final String memorySliceSuffix : memorySliceSuffixes) {
			final Map<String, String> oldIdToNewId = memoryArrays.stream()
					.collect(Collectors.toMap(Function.identity(), x -> x + memorySliceSuffix));
			res.add(renameSpecification(oldIdToNewId, memorySliceSuffix, p));
		}
		return res;
	}

	private static Procedure renameSpecification(final Map<String, String> oldIdToNewId, final String memorySliceSuffix,
			final Procedure p) {
		if (p.getBody() != null) {
			throw new AssertionError("Method not meant for Procedures with implementation");
		}
		final IdentifierReplacer ir = new IdentifierReplacer(oldIdToNewId);
		final Specification[] newSpec = ir.processSpecifications(p.getSpecification());
		final Procedure res = new Procedure(p.getLoc(), p.getAttributes(), p.getIdentifier() + memorySliceSuffix,
				p.getTypeParams(), p.getInParams(), p.getOutParams(), newSpec, null);
		ModelUtils.copyAnnotations(p, res);
		return res;
	}

	public List<VariableDeclaration> duplicateMemoryArrayVarDecl(final Collection<String> memoryArrays,
			final Collection<String> memorySliceSuffixes, final Declaration d) {
		if (d instanceof VariableDeclaration) {
			final VariableDeclaration varDecl = (VariableDeclaration) d;
			if (varDecl.getVariables().length == 1) {
				final VarList varList = varDecl.getVariables()[0];
				if (isSingleIdList(MemorySliceUtils.MEMORY_INT, varList)) {
					return duplicateMemoryArrayVarDecl(varDecl, new String[] { MemorySliceUtils.MEMORY_INT },
							memorySliceSuffixes);
				}
			} else if (varDecl.getVariables().length == 2) {
				final VarList varList0 = varDecl.getVariables()[0];
				final VarList varList1 = varDecl.getVariables()[1];
				if (isSingleIdList(MemorySliceUtils.MEMORY_POINTER_BASE, varList0)
						&& isSingleIdList(MemorySliceUtils.MEMORY_POINTER_OFFSET, varList1)) {
					return duplicateMemoryArrayVarDecl(varDecl,
							new String[] { MemorySliceUtils.MEMORY_POINTER_BASE, MemorySliceUtils.MEMORY_POINTER_OFFSET },
							memorySliceSuffixes);
				}

			}
		}
		return null;
	}

	private boolean isSingleIdList(final String id, final VarList varList) {
		final String[] ids = varList.getIdentifiers();
		if (ids.length == 1) {
			return ids[0].equals(id);
		}
		return false;
	}

	private static List<VariableDeclaration> duplicateMemoryArrayVarDecl(final VariableDeclaration varDecl,
			final String[] memoryArrayIds, final Collection<String> memorySliceSuffixes) {
		final List<VariableDeclaration> newHeapVarDecls = new ArrayList<>();
		for (final String memorySliceSuffix : memorySliceSuffixes) {
			newHeapVarDecls.add(renameMemoryArray(varDecl, memoryArrayIds, memorySliceSuffix));
		}
		return newHeapVarDecls;
	}

	private static VariableDeclaration renameMemoryArray(final VariableDeclaration oldVarDecl, final String[] memoryArrayIds,
			final String memorySliceSuffix) {
		assert oldVarDecl.getVariables().length == memoryArrayIds.length;
		final VarList[] variables = new VarList[oldVarDecl.getVariables().length];
		for (int i = 0; i < oldVarDecl.getVariables().length; i++) {
			final VarList varList = oldVarDecl.getVariables()[i];
			final VarList newVarList = new VarList(varList.getLoc(),
					new String[] { memoryArrayIds[i] + memorySliceSuffix }, varList.getType(),
					varList.getWhereClause());
			ModelUtils.copyAnnotations(varList, newVarList);
			variables[i] = newVarList;

		}
		final VariableDeclaration newVarDecl = new VariableDeclaration(oldVarDecl.getLoc(), oldVarDecl.getAttributes(),
				variables);
		ModelUtils.copyAnnotations(oldVarDecl, newVarDecl);
		return newVarDecl;
	}


}
