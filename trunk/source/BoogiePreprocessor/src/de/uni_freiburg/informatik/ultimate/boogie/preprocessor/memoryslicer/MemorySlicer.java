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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MemorySlicer implements IUnmanagedObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;

	private final AddressStoreFactory mAsfac;
	private final ILogger mLogger;

	public MemorySlicer(final BoogiePreprocessorBacktranslator translator, final ILogger logger) {
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
			final Map<String, Procedure> map = constructIdToImplementation(unit.getDeclarations());

			try {
				final ArrayDeque<Declaration> newDecls = tryToSliceMemory(unit, map);
				unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			} catch (final MemorySliceException e) {
				// memory slicing failed, do not change anything
				mLogger.warn("Omit memory slicing because it failed with the following exception: " + e.getMessage());
			}
			return false;
		}
		return true;
	}

	private ArrayDeque<Declaration> tryToSliceMemory(final Unit unit, final Map<String, Procedure> map)
			throws AssertionError {
		final AliasAnalysis aa = new AliasAnalysis(mAsfac, map);
		final MayAlias ma = aa.aliasAnalysis(unit);
		final Map<AddressStore, Integer> repToArray = constructMemorySliceMapping(aa, ma);

		final Collection<String> memorySliceSuffixes = new ArrayList<>();
		for (final Integer memorySliceId : repToArray.values()) {
			final String memorySliceSuffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceId);
			memorySliceSuffixes.add(memorySliceSuffix);
		}

		final HashRelation<String, Integer> procedureToDirectlyModifiedMemorySlices = computeProcedureToDirectlyModifiedSlices(
				aa, ma, repToArray);

		final HashRelation<String, Integer> procedureToModifiedMemorySlices = computeProcedureToModifiedSlices(aa,
				procedureToDirectlyModifiedMemorySlices);

		final ArrayDeque<Declaration> newDecls = new ArrayDeque<>();
		final MemoryArrayReplacer har = new MemoryArrayReplacer(mAsfac, ma, repToArray,
				procedureToModifiedMemorySlices);
		for (final Declaration d : unit.getDeclarations()) {
			final List<String> memoryArrays = Arrays.asList(new String[] { MemorySliceUtils.MEMORY_POINTER,
					MemorySliceUtils.MEMORY_INT, MemorySliceUtils.MEMORY_REAL });
			final List<VariableDeclaration> newMemoryVarDecls = duplicateMemoryArrayVarDecl(memoryArrays,
					memorySliceSuffixes, d);
			if (newMemoryVarDecls != null) {
				newDecls.addAll(newMemoryVarDecls);
			} else if (d instanceof Procedure) {
				final Procedure proc = (Procedure) d;
				if (isUltimateBasicMemoryReadWriteProcedure(proc)
						|| isUltimateMemoryReadWriteProcedureWithImplementation(proc)) {
					final List<Procedure> duplicates = duplicateProcedure(memoryArrays, memorySliceSuffixes,
							(Procedure) d);
					newDecls.addAll(duplicates);
				} else if (isUltimateMemoryAllocationProcedure(proc)) {
					// nothing has to be changed here
					newDecls.add(proc);
				} else if (isUltimateMemoryConcurrencyProcedure(proc)) {
					// nothing has to be changed here
					newDecls.add(proc);
				} else {
					if (proc.getSpecification() != null) {
						final Specification[] specs = proc.getSpecification();
						for (final Specification spec : specs) {
							if (!(spec instanceof ModifiesSpecification)) {
								throw new MemorySliceException(String.format(
										"Unsupported: Procedure %s is not part of the Ultimate memory model but has specification other that is not a ModifiesSpecification",
										proc.getIdentifier()));
							}
						}
					}
					final Declaration newDecl = har.processDeclaration(proc);
					newDecls.add(newDecl);
				}
			} else {
				newDecls.add(d);
			}
		}
		mLogger.info(har.generateLogMessage());
		return newDecls;
	}

	public HashRelation<String, Integer> computeProcedureToModifiedSlices(final AliasAnalysis aa,
			final HashRelation<String, Integer> procedureToDirectlyModifiedMemorySlices) {
		final HashRelation<String, Integer> procedureToModifiedMemorySlices = new HashRelation<>(
				procedureToDirectlyModifiedMemorySlices);
		final LinkedHashSet<String> worklist = new LinkedHashSet<>();
		worklist.addAll(procedureToDirectlyModifiedMemorySlices.getDomain());
		while (!worklist.isEmpty()) {
			final String proc = worklist.iterator().next();
			worklist.remove(proc);

			for (final String caller : aa.getReverseCallgraph().getImage(proc)) {
				if (!caller.equals(proc)) {
					boolean someChange = false;
					for (final Integer modifiedSlice : procedureToDirectlyModifiedMemorySlices.getImage(proc)) {
						someChange |= procedureToModifiedMemorySlices.addPair(caller, modifiedSlice);
					}
					if (someChange) {
						worklist.add(caller);
					}
				}
			}
		}
		return procedureToModifiedMemorySlices;
	}

	public HashRelation<String, Integer> computeProcedureToDirectlyModifiedSlices(final AliasAnalysis aa,
			final MayAlias ma, final Map<AddressStore, Integer> repToArray) {
		final HashRelation<String, Integer> procedureToDirectlyModifiedMemorySlices = new HashRelation<>();
		{
			final HashRelation<String, PointerBase> procedureToWritePointers = aa.getProcedureToWritePointers();
			for (final String proc : procedureToWritePointers.getDomain()) {
				for (final PointerBase pb : procedureToWritePointers.getImage(proc)) {
					final AddressStore rep = ma.getAddressStores().find(pb);
					final Integer sliceNumber = repToArray.get(rep);
					if (sliceNumber == null) {
						throw new MemorySliceException("Unknown PointerBase " + pb);
					}
					procedureToDirectlyModifiedMemorySlices.addPair(proc, sliceNumber);
				}
			}
		}
		return procedureToDirectlyModifiedMemorySlices;
	}

	public Map<AddressStore, Integer> constructMemorySliceMapping(final AliasAnalysis aa, final MayAlias ma) {
		final Map<AddressStore, Integer> repToArray = new HashMap<>();
		{
			final UnionFind<AddressStore> uf = ma.getAddressStores();
			for (final AddressStore elem : uf.getAllElements()) {
				if (elem instanceof PointerBase) {
					if (AliasAnalysis.isNullPointer((PointerBase) elem)) {
						assert uf.find(elem) == elem && uf.getEquivalenceClassMembers(elem).size() == 1;
					}
				}
			}
			int ctr = 0;
			final Set<AddressStore> representativesOfAccesses = new HashSet<>();
			for (final PointerBase tmp : aa.getAccessAddresses()) {
				final AddressStore rep = uf.find(tmp);
				Objects.requireNonNull(rep, "Cannot find pointer: " + tmp);
				representativesOfAccesses.add(rep);
			}
			for (final AddressStore rep : representativesOfAccesses) {
				repToArray.put(rep, ctr);
				ctr++;
			}
		}
		return repToArray;
	}

	private Map<String, Procedure> constructIdToImplementation(final Declaration[] declarations) {
		final Map<String, Procedure> result = new HashMap<>();
		for (final Declaration decl : declarations) {
			if (decl instanceof Procedure) {
				final Procedure p = (Procedure) decl;
				if (p.getBody() != null) {
					result.put(p.getIdentifier(), p);
				}
			}
		}
		return result;
	}

	private static boolean isUltimateBasicMemoryReadWriteProcedure(final Procedure proc) {
		final List<String> ultimateMemoryModifyingProcedures = toList(MemorySliceUtils.WRITE_POINTER,
				MemorySliceUtils.WRITE_INT, MemorySliceUtils.WRITE_REAL, MemorySliceUtils.WRITE_INIT_POINTER,
				MemorySliceUtils.WRITE_INIT_INT, MemorySliceUtils.WRITE_INIT_REAL,
				MemorySliceUtils.WRITE_UNCHECKED_POINTER, MemorySliceUtils.WRITE_UNCHECKED_INT,
				MemorySliceUtils.WRITE_UNCHECKED_REAL, MemorySliceUtils.READ_POINTER, MemorySliceUtils.READ_INT,
				MemorySliceUtils.READ_REAL, MemorySliceUtils.READ_UNCHECKED_POINTER,
				MemorySliceUtils.READ_UNCHECKED_INT, MemorySliceUtils.READ_UNCHECKED_REAL);
		assert ultimateMemoryModifyingProcedures.size() == 15;
		for (final String ummp : ultimateMemoryModifyingProcedures) {
			if (proc.getIdentifier().startsWith(ummp)) {
				return true;
			}
		}
		return false;
	}

	public static boolean isUltimateMemoryReadWriteProcedureWithImplementation(final Procedure proc) {
		final List<String> ultimateMemoryModifyingProcedures = toList(MemorySliceUtils.ULTIMATE_C_MEMSET,
				MemorySliceUtils.ULTIMATE_C_MEMCPY, MemorySliceUtils.ULTIMATE_C_MEMMOVE,
				MemorySliceUtils.ULTIMATE_C_STRCPY, MemorySliceUtils.ULTIMATE_C_REALLOC);
		for (final String ummp : ultimateMemoryModifyingProcedures) {
			if (proc.getIdentifier().startsWith(ummp)) {
				return true;
			}
		}
		return false;
	}

	private static boolean isUltimateMemoryAllocationProcedure(final Procedure proc) {
		final List<String> ultimateMemoryAllocationProcedures = toList(MemorySliceUtils.ALLOC_INIT,
				MemorySliceUtils.ALLOC_ON_HEAP, MemorySliceUtils.ALLOC_ON_STACK, MemorySliceUtils.ULTIMATE_DEALLOC);
		for (final String umap : ultimateMemoryAllocationProcedures) {
			if (proc.getIdentifier().startsWith(umap)) {
				return true;
			}
		}
		return false;
	}

	private static boolean isUltimateMemoryConcurrencyProcedure(final Procedure proc) {
		final List<String> ultimateMemoryAllocationProcedures = toList(MemorySliceUtils.PTHREADS_FORK_COUNT,
				MemorySliceUtils.PTHREADS_MUTEX, MemorySliceUtils.PTHREADS_MUTEX_LOCK,
				MemorySliceUtils.PTHREADS_MUTEX_UNLOCK, MemorySliceUtils.PTHREADS_MUTEX_TRYLOCK,
				MemorySliceUtils.PTHREADS_RWLOCK, MemorySliceUtils.PTHREADS_RWLOCK_READLOCK,
				MemorySliceUtils.PTHREADS_RWLOCK_WRITELOCK, MemorySliceUtils.PTHREADS_RWLOCK_UNLOCK);
		for (final String umap : ultimateMemoryAllocationProcedures) {
			if (proc.getIdentifier().startsWith(umap)) {
				return true;
			}
		}
		return false;
	}

	public static ModifiesSpecification reviseModifiesSpec(final Collection<Integer> memorySliceIds,
			final ModifiesSpecification oldMs, final String... memoryInt) {
		final VariableLHS[] oldIds = oldMs.getIdentifiers();
		final List<VariableLHS> newIds = new ArrayList<>();
		for (final VariableLHS oldId : oldIds) {
			if (Arrays.asList(memoryInt).contains(oldId.getIdentifier())) {
				for (final Integer memorySliceId : memorySliceIds) {
					final String memorySliceSuffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceId);
					final VariableLHS vlhs = new VariableLHS(oldId.getLoc(), oldId.getType(),
							oldId.getIdentifier() + memorySliceSuffix, oldId.getDeclarationInformation());
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
		final IdentifierReplacer ir = new IdentifierReplacer(oldIdToNewId, p.getIdentifier(), memorySliceSuffix);
		final Body newBody;
		if (p.getBody() == null) {
			newBody = null;
		} else {
			newBody = ir.processBody(p.getBody());
		}
		final Specification[] newSpecs;
		if (p.getSpecification() == null) {
			newSpecs = null;
		} else {
			newSpecs = ir.processSpecifications(p.getSpecification());
		}
		final Procedure res = new Procedure(p.getLoc(), p.getAttributes(), p.getIdentifier() + memorySliceSuffix,
				p.getTypeParams(), p.getInParams(), p.getOutParams(), newSpecs, newBody);
		ModelUtils.copyAnnotations(p, res);
		return res;
	}

	public List<VariableDeclaration> duplicateMemoryArrayVarDecl(final Collection<String> memoryArrays,
			final Collection<String> memorySliceSuffixes, final Declaration d) {
		if (d instanceof VariableDeclaration) {
			final VariableDeclaration varDecl = (VariableDeclaration) d;
			if (varDecl.getVariables().length == 1) {
				final VarList varList = varDecl.getVariables()[0];
				if (isSingleIdList(MemorySliceUtils.MEMORY_POINTER, varList)) {
					return duplicateMemoryArrayVarDecl(varDecl, new String[] { MemorySliceUtils.MEMORY_POINTER },
							memorySliceSuffixes);
				}
				if (isSingleIdList(MemorySliceUtils.MEMORY_INT, varList)) {
					return duplicateMemoryArrayVarDecl(varDecl, new String[] { MemorySliceUtils.MEMORY_INT },
							memorySliceSuffixes);
				}
				if (isSingleIdList(MemorySliceUtils.MEMORY_REAL, varList)) {
					return duplicateMemoryArrayVarDecl(varDecl, new String[] { MemorySliceUtils.MEMORY_REAL },
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
		final List<VariableDeclaration> newMemoryVarDecls = new ArrayList<>();
		for (final String memorySliceSuffix : memorySliceSuffixes) {
			newMemoryVarDecls.add(renameMemoryArray(varDecl, memoryArrayIds, memorySliceSuffix));
		}
		return newMemoryVarDecls;
	}

	private static VariableDeclaration renameMemoryArray(final VariableDeclaration oldVarDecl,
			final String[] memoryArrayIds, final String memorySliceSuffix) {
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
