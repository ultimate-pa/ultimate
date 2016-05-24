/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IType;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IdentifierTranslator;

/**
 * Main class for the translation from Boogie to SMT. Constructs other Objects needed for this translation.
 * 
 * @author Matthias Heizmann
 * 
 */
public class Boogie2SMT {

	/**
	 * if set to true array access returns arbitrary values array store returns arbitrary arrays
	 */
	private final boolean mBlackHoleArrays;

	private final BoogieDeclarations mBoogieDeclarations;
	private Script mScript;

	private final TypeSortTranslator mTypeSortTranslator;
	private final IOperationTranslator mOperationTranslator;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final VariableManager mVariableManager;
	private final Expression2Term mExpression2Term;
	private final Term2Expression mTerm2Expression;

	private final Statements2TransFormula mStatements2TransFormula;

	private final ConstOnlyIdentifierTranslator mConstOnlyIdentifierTranslator;

	private final Collection<Term> mAxioms;

	private IUltimateServiceProvider mServices;

	public Boogie2SMT(Script script, BoogieDeclarations boogieDeclarations, boolean blackHoleArrays,
			boolean bitvectorInsteadOfInt, IUltimateServiceProvider services) {
		mServices = services;
		mBlackHoleArrays = blackHoleArrays;
		mBoogieDeclarations = boogieDeclarations;
		mScript = script;
		mVariableManager = new VariableManager(mScript, mServices);

		if (bitvectorInsteadOfInt) {
			mTypeSortTranslator = new TypeSortTranslatorBitvectorWorkaround(boogieDeclarations.getTypeDeclarations(),
					mScript, mBlackHoleArrays, mServices);
			mBoogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, mScript, mTypeSortTranslator);
			mConstOnlyIdentifierTranslator = new ConstOnlyIdentifierTranslator();
			mOperationTranslator = new BitvectorWorkaroundOperationTranslator(mBoogie2SmtSymbolTable, mScript);
			mExpression2Term = new Expression2Term(mServices, mScript, mTypeSortTranslator, mBoogie2SmtSymbolTable,
					mOperationTranslator, mVariableManager);
		} else {
			mTypeSortTranslator = new TypeSortTranslator(boogieDeclarations.getTypeDeclarations(), mScript,
					mBlackHoleArrays, mServices);
			mBoogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, mScript, mTypeSortTranslator);

			mConstOnlyIdentifierTranslator = new ConstOnlyIdentifierTranslator();
			mOperationTranslator = new DefaultOperationTranslator(mBoogie2SmtSymbolTable, mScript);
			mExpression2Term = new Expression2Term(mServices, mScript, mTypeSortTranslator, mBoogie2SmtSymbolTable,
					mOperationTranslator, mVariableManager);
		}

		mAxioms = new ArrayList<Term>(boogieDeclarations.getAxioms().size());
		for (Axiom decl : boogieDeclarations.getAxioms()) {
			Term term = declareAxiom(decl, mExpression2Term);
			mAxioms.add(term);
		}
		mStatements2TransFormula = new Statements2TransFormula(this, mServices, mExpression2Term);
		mTerm2Expression = new Term2Expression(mTypeSortTranslator, mBoogie2SmtSymbolTable);

	}

	public VariableManager getVariableManager() {
		return mVariableManager;
	}

	public Script getScript() {
		return mScript;
	}

	public Term2Expression getTerm2Expression() {
		return mTerm2Expression;
	}

	static String quoteId(String id) {
		// return Term.quoteId(id);
		return id;
	}

	public Boogie2SmtSymbolTable getBoogie2SmtSymbolTable() {
		return mBoogie2SmtSymbolTable;
	}

	public Statements2TransFormula getStatements2TransFormula() {
		return mStatements2TransFormula;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}

	public TypeSortTranslator getTypeSortTranslator() {
		return mTypeSortTranslator;
	}

	ConstOnlyIdentifierTranslator getConstOnlyIdentifierTranslator() {
		return mConstOnlyIdentifierTranslator;
	}

	public Collection<Term> getAxioms() {
		return mAxioms;
	}

	private Term declareAxiom(Axiom ax, Expression2Term expression2term) {
		IdentifierTranslator[] its = new IdentifierTranslator[] { getConstOnlyIdentifierTranslator() };
		Term term = expression2term.translateToTerm(its, ax.getFormula()).getTerm();
		mScript.assertTerm(term);
		return term;
	}

	public static void reportUnsupportedSyntax(BoogieASTNode BoogieASTNode, String longDescription,
			IUltimateServiceProvider services) {
		UnsupportedSyntaxResult<BoogieASTNode> result = new UnsupportedSyntaxResult<BoogieASTNode>(BoogieASTNode,
				ModelCheckerUtils.PLUGIN_ID, services.getBacktranslationService(), longDescription);
		services.getResultService().reportResult(ModelCheckerUtils.PLUGIN_ID, result);
		services.getProgressMonitorService().cancelToolchain();
	}

	/**
	 * Use with caution! Construct auxiliary variables only if you need then in the whole verification process.
	 * Construct auxiliary variables only if the assertion stack of the script is at the lowest level. Auxiliary
	 * variables are not supported in any backtranslation.
	 */
	public BoogieNonOldVar constructAuxiliaryGlobalBoogieVar(String identifier, String procedure, IType iType,
			VarList varList) {

		return mBoogie2SmtSymbolTable.constructAuxiliaryGlobalBoogieVar(identifier, procedure, iType, varList);
	}

	class ConstOnlyIdentifierTranslator implements IdentifierTranslator {

		@Override
		public Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			if (declInfo.getStorageClass() != StorageClass.GLOBAL) {
				throw new AssertionError();
			}
			Term result = mBoogie2SmtSymbolTable.getBoogieConst(id).getDefaultConstant();
			if (result == null) {
				throw new AssertionError();
			}
			return result;
		}
	}
}
