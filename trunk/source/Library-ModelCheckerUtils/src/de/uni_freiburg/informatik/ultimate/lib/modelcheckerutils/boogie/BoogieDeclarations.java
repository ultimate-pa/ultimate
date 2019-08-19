/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Objects that stores all global declarations and procedure contracts and makes them available as Collections, Sets,
 * and Maps.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BoogieDeclarations {

	private final ILogger mLogger;

	private final List<Axiom> mAxioms = new ArrayList<>();
	private final List<TypeDeclaration> mTypeDeclarations = new ArrayList<>();
	private final List<ConstDeclaration> mConstDeclarations = new ArrayList<>();
	private final List<FunctionDeclaration> mFunctionDeclarations = new ArrayList<>();
	private final List<VariableDeclaration> mGlobalVarDeclarations = new ArrayList<>();

	/**
	 * Maps a procedure name to the Procedure object that contains the specification of the procedure.
	 */
	private final Map<String, Procedure> mProcSpecification = new HashMap<>();

	/**
	 * Maps a procedure name to the Procedure object that contains the implementation of the procedure.
	 */
	private final Map<String, Procedure> mProcImplementation = new HashMap<>();

	/**
	 * Maps a procedure name to the requires clauses of the procedure
	 */
	private final Map<String, List<RequiresSpecification>> mRequires = new HashMap<>();

	/**
	 * Maps a procedure name to the requires clauses of the procedure which are not free. (A requires clause is not free
	 * if we have to proof that it holds.)
	 */
	private final Map<String, List<RequiresSpecification>> mRequiresNonFree = new HashMap<>();

	/**
	 * Maps a procedure name to the ensures clauses of the procedure
	 */
	private final Map<String, List<EnsuresSpecification>> mEnsures = new HashMap<>();

	/**
	 * Maps a procedure name to the ensures clauses of the procedure which are not free. (A ensures clause is not free
	 * if we have to proof that it holds.)
	 */
	private final Map<String, List<EnsuresSpecification>> mEnsuresNonFree = new HashMap<>();

	/**
	 * Maps a procedure name to the set of global variables which may be modified by the procedure. The set of variables
	 * is represented as a map where the identifier of the variable is mapped to the type of the variable.
	 */
	private final Map<String, Set<String>> mModifiedVars = new HashMap<>();

	public BoogieDeclarations(final Collection<Declaration> decls, final ILogger logger) {
		mLogger = logger;
		for (final Declaration decl : decls) {
			if (decl instanceof Axiom) {
				mAxioms.add((Axiom) decl);
			} else if (decl instanceof TypeDeclaration) {
				mTypeDeclarations.add((TypeDeclaration) decl);
			} else if (decl instanceof ConstDeclaration) {
				mConstDeclarations.add((ConstDeclaration) decl);
			} else if (decl instanceof FunctionDeclaration) {
				mFunctionDeclarations.add((FunctionDeclaration) decl);
			} else if (decl instanceof VariableDeclaration) {
				mGlobalVarDeclarations.add((VariableDeclaration) decl);
			} else if (decl instanceof Procedure) {
				final Procedure proc = (Procedure) decl;
				if (proc.getSpecification() != null && proc.getBody() != null) {
					mLogger.info(String.format(
							"Specification and implementation of procedure %s given in one single declaration",
							proc.getIdentifier()));
				}

				if (proc.getSpecification() != null) {
					mLogger.info("Found specification of procedure " + proc.getIdentifier());
					if (mProcSpecification.containsKey(proc.getIdentifier())) {
						throw new UnsupportedOperationException(
								"Procedure" + proc.getIdentifier() + "declarated twice");
					}
					mProcSpecification.put(proc.getIdentifier(), proc);
				}
				if (proc.getBody() != null) {
					mLogger.info("Found implementation of procedure " + proc.getIdentifier());
					if (mProcImplementation.containsKey(proc.getIdentifier())) {
						throw new UnsupportedOperationException(
								"File " + "contains two implementations of procedure" + proc.getIdentifier());
					}
					mProcImplementation.put(proc.getIdentifier(), proc);
				}
			} else {
				throw new AssertionError("Unknown Declaration" + decl);
			}
		}
		for (final Procedure proc : mProcSpecification.values()) {
			extractContract(proc.getIdentifier());
		}
	}

	public BoogieDeclarations(final Declaration[] decls, final ILogger logger) {
		this(Arrays.asList(decls), logger);
	}

	public BoogieDeclarations(final Unit unit, final ILogger logger) {
		this(unit.getDeclarations(), logger);
	}

	/**
	 * Get the contract (requires, ensures, modified variables) of a procedure specification. Write it to mEnsures,
	 * mEnsuresNonFree, mRequires, mRequiresNonFree and mModifiedVars.
	 */
	private void extractContract(final String procId) {
		final Procedure procSpec = mProcSpecification.get(procId);
		final Procedure procImpl = mProcImplementation.get(procId);

		Specification[] specifications;
		if (procSpec != procImpl && procImpl != null) {
			/*
			 * Special case where specification and implementation are given by different procedure objects. In this
			 * case we rename the contracts of the specification to make them compatible with the variables of the
			 * implementation.
			 */
			final RenameProcedureSpec renamer = new RenameProcedureSpec();
			specifications = renamer.renameSpecs(procSpec, procImpl);
		} else {
			specifications = procSpec.getSpecification();
		}

		final List<EnsuresSpecification> ensures = new ArrayList<>();
		final List<EnsuresSpecification> ensuresNonFree = new ArrayList<>();
		final List<RequiresSpecification> requires = new ArrayList<>();
		final List<RequiresSpecification> requiresNonFree = new ArrayList<>();
		final Set<String> modifiedVars = new HashSet<>();
		for (final Specification spec : specifications) {
			if (spec instanceof EnsuresSpecification) {
				final EnsuresSpecification ensSpec = (EnsuresSpecification) spec;
				ensures.add(ensSpec);
				if (!ensSpec.isFree()) {
					ensuresNonFree.add(ensSpec);
				}
			} else if (spec instanceof RequiresSpecification) {
				final RequiresSpecification recSpec = (RequiresSpecification) spec;
				requires.add(recSpec);
				if (!recSpec.isFree()) {
					requiresNonFree.add(recSpec);
				}
			} else if (spec instanceof LoopInvariantSpecification) {
				mLogger.debug(
						"Found LoopInvariantSpecification" + spec + "but this plugin does not use loop invariants.");
				throw new IllegalArgumentException("LoopInvariantSpecification may not occur in procedure constract");
			} else if (spec instanceof ModifiesSpecification) {
				final ModifiesSpecification modSpec = (ModifiesSpecification) spec;
				for (final VariableLHS var : modSpec.getIdentifiers()) {
					final String ident = var.getIdentifier();
					modifiedVars.add(ident);
				}
			} else {
				throw new UnsupportedOperationException("Unknown type of specification)");
			}
			mEnsures.put(procId, ensures);
			mEnsuresNonFree.put(procId, ensuresNonFree);
			mRequires.put(procId, requires);
			mRequiresNonFree.put(procId, requiresNonFree);
		}
		mModifiedVars.put(procId, modifiedVars);
	}

	public List<Axiom> getAxioms() {
		return mAxioms;
	}

	public List<TypeDeclaration> getTypeDeclarations() {
		return mTypeDeclarations;
	}

	public List<ConstDeclaration> getConstDeclarations() {
		return mConstDeclarations;
	}

	public List<FunctionDeclaration> getFunctionDeclarations() {
		return mFunctionDeclarations;
	}

	public List<VariableDeclaration> getGlobalVarDeclarations() {
		return mGlobalVarDeclarations;
	}

	public Map<String, Procedure> getProcSpecification() {
		return mProcSpecification;
	}

	public Map<String, Procedure> getProcImplementation() {
		return mProcImplementation;
	}

	public Map<String, List<RequiresSpecification>> getRequires() {
		return mRequires;
	}

	public Map<String, List<RequiresSpecification>> getRequiresNonFree() {
		return mRequiresNonFree;
	}

	public Map<String, List<EnsuresSpecification>> getEnsures() {
		return mEnsures;
	}

	public Map<String, List<EnsuresSpecification>> getEnsuresNonFree() {
		return mEnsuresNonFree;
	}

	public Map<String, Set<String>> getModifiedVars() {
		return mModifiedVars;
	}

}
