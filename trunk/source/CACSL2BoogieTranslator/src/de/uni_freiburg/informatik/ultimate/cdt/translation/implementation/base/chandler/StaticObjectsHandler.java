/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * This class manages objects (in the meaning that the word has in the C-standard) with static storage duration.
 * <p>
 * Those objects typically require declaration of a global variable in the Boogie code and sometimes initialization code
 * in the procedure ULTIMATE.Init.
 * <p>
 * Examples of such objects are:
 * <li>variables declared as 'static' in the C program
 * <li>global variables in the C program
 * <li>string literals in the C program that are on-heap in our Boogie program
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StaticObjectsHandler {

	private final List<Statement> mStatementsForUltimateInit;
	private final List<ConstDeclaration> mConstDeclarations = new ArrayList<>();
	private final List<Axiom> mAxioms = new ArrayList<>();

	private boolean mIsFrozen;
	private int mDeclCounter;
	private final HashRelation<String, Triple<VariableDeclaration, CDeclaration, Integer>> mGlobalVarsForCVars =
			new HashRelation<>();
	private final List<VariableDeclaration> mGlobalVarsWithoutCVar = new ArrayList<>();

	private final Map<TypeDeclaration, CDeclaration> mTypeDeclarationToCDeclaration;
	private final Map<String, TypeDeclaration> mIncompleteType2TypeDecl;

	private final ILogger mLogger;

	public StaticObjectsHandler(final ILogger logger) {
		mStatementsForUltimateInit = new ArrayList<>();
		mTypeDeclarationToCDeclaration = new LinkedHashMap<>();
		mIncompleteType2TypeDecl = new HashMap<>();
		mIsFrozen = false;
		mLogger = logger;
	}

	/**
	 * Returns all Boogie declarations that need to be added to the translated program in global scope
	 *
	 */
	public List<Declaration> getGlobalDeclarations() {
		assert mIsFrozen;
		final List<Declaration> globalDecls = new ArrayList<>();
		globalDecls.addAll(mTypeDeclarationToCDeclaration.keySet());
		globalDecls.addAll(mConstDeclarations);
		globalDecls.addAll(mAxioms);
		globalDecls.addAll(mGlobalVarsWithoutCVar);
		for (final Pair<VariableDeclaration, CDeclaration> pair : computeSuitableGlobalVarDecls()) {
			globalDecls.add(pair.getFirst());
		}
		return globalDecls;
	}

	public List<Statement> getStatementsForUltimateInit() {
		assert mIsFrozen;
		return mStatementsForUltimateInit;
	}

	public void freeze() {
		assert !mIsFrozen : "called freeze but is already frozen";
		mIsFrozen = true;
	}

	public void addGlobalTypeDeclaration(final TypeDeclaration boogieDec, final CDeclaration cDec) {
		assert boogieDec != null && cDec != null : "Part of global type declaration is null";
		mTypeDeclarationToCDeclaration.put(boogieDec, cDec);
		final CType cType = cDec.getType();
		if (cType.isIncomplete() && !cDec.getType().getUnderlyingType().isVoidType()) {
			if (cType instanceof CStructOrUnion) {
				mIncompleteType2TypeDecl.put(((CStructOrUnion) cType).getName(), boogieDec);
			} else if (cType instanceof CEnum) {
				mIncompleteType2TypeDecl.put(((CEnum) cType).getName(), boogieDec);
			} else {
				throw new AssertionError("missing support for global incomplete " + cType);
			}
		}
	}

	public void addGlobalVariableDeclaration(final VariableDeclaration boogieDec, final CDeclaration cDec) {
		mGlobalVarsForCVars.addPair(cDec.getName(), new Triple<>(boogieDec, cDec, mDeclCounter));
		mDeclCounter++;
	}

	/**
	 * If the same variable is declared multiple times (within the same scope), we only keep one declaration. If one of
	 * them has an initializer, we keep that one.
	 */
	public List<Pair<VariableDeclaration, CDeclaration>> computeSuitableGlobalVarDecls() {
		// Matthias 20221110: Unfortunately, we cannot require that this object is frozen.
		// This method is called by the PostProcessor and something modifies this object afterwards.
		final List<Triple<VariableDeclaration, CDeclaration, Integer>> result = new ArrayList<>();
		for (final String id : mGlobalVarsForCVars.getDomain()) {
			final Set<Triple<VariableDeclaration, CDeclaration, Integer>> decls = mGlobalVarsForCVars.getImage(id);
			final Triple<VariableDeclaration, CDeclaration, Integer> varDecl = computeSuitableVarDecl(decls);
			result.add(varDecl);
		}
		return result.stream().sorted(Comparator.comparingInt(Triple::getThird))
				.map(trip -> new Pair<>(trip.getFirst(), trip.getSecond())).collect(Collectors.toList());
	}

	private Triple<VariableDeclaration, CDeclaration, Integer>
			computeSuitableVarDecl(final Set<Triple<VariableDeclaration, CDeclaration, Integer>> decls) {
		if (decls.size() == 1) {
			return decls.iterator().next();
		} else {
			Triple<VariableDeclaration, CDeclaration, Integer> suiteableDecl = null;
			for (final Triple<VariableDeclaration, CDeclaration, Integer> pair : decls) {
				if (pair.getSecond().getInitializer() != null) {
					if (suiteableDecl == null) {
						suiteableDecl = pair;
					} else {
						throw new AssertionError("Two decls with initializer " + pair.getSecond().getName());
					}
				}
			}
			if (suiteableDecl == null) {
				// no declaration has an initializer, pick some
				suiteableDecl = decls.iterator().next();
			}
			return suiteableDecl;
		}
	}

	public void addGlobalConstDeclaration(final ConstDeclaration cd, final CDeclaration cDeclaration,
			final Axiom axiom) {
		mConstDeclarations.add(cd);
		if (axiom != null) {
			mAxioms.add(axiom);
		}
	}

	/**
	 * mTypeDeclarationToCDeclaration may contain type declarations that stem from typedefs using an incomplete struct
	 * type. This method is called when the struct type is completed.
	 *
	 * @param cvar
	 * @param incompleteStruct
	 */
	public void completeTypeDeclaration(final String incompleteType, final CType completedType,
			final ITypeHandler typeHandler) {
		final TypeDeclaration oldBoogieDec = mIncompleteType2TypeDecl.remove(incompleteType);
		if (oldBoogieDec == null) {
			// already completed
			// throw new AssertionError("can only complete incomplete types: " + incompleteType);
			return;
		}
		final CDeclaration oldCDec = mTypeDeclarationToCDeclaration.get(oldBoogieDec);
		assert oldCDec != null : "We have a Boogie declaration, we should also have a C declaration: "
				+ oldBoogieDec.getIdentifier();

		final TypeDeclaration newBoogieDec = new TypeDeclaration(oldBoogieDec.getLocation(),
				oldBoogieDec.getAttributes(), oldBoogieDec.isFinite(), oldBoogieDec.getIdentifier(),
				oldBoogieDec.getTypeParams(), typeHandler.cType2AstType(oldBoogieDec.getLocation(), completedType));

		mTypeDeclarationToCDeclaration.remove(oldBoogieDec);
		addGlobalTypeDeclaration(newBoogieDec, oldCDec);
	}

	/**
	 * Add a VariableDeclaration for the global Boogie scope without an associated CDeclaration. Normally, the
	 * CDeclaration would be used for initializing the variable; in this case, initialization code can be added manually
	 * via addStatementsForUltimateInit(..).
	 *
	 * @param varDec
	 */
	public void addGlobalVarDeclarationWithoutCDeclaration(final VariableDeclaration varDec) {
		mGlobalVarsWithoutCVar.add(varDec);
	}

	public void addStatementsForUltimateInit(final List<Statement> stmts) {
		assert !mIsFrozen;
		for (final Statement stmt : stmts) {
			mStatementsForUltimateInit.add(stmt);
		}
	}
}
