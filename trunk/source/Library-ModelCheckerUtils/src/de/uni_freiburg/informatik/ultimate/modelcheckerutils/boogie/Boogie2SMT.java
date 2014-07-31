package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Main class for the translation from Boogie to SMT. Constructs other Objects
 * needed for this translation.
 * 
 * @author Matthias Heizmann
 * 
 */
public class Boogie2SMT {

	/**
	 * if set to true array access returns arbitrary values array store returns
	 * arbitrary arrays
	 */
	private final boolean m_BlackHoleArrays;

	private final BoogieDeclarations m_BoogieDeclarations;
	private Script m_Script;

	private final TypeSortTranslator m_TypeSortTranslator;
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;
	private final VariableManager m_VariableManager;
	private final Term2Expression m_Term2Expression;

	private final Statements2TransFormula m_Statements2TransFormula;

	private final ConstOnlyIdentifierTranslator m_ConstOnlyIdentifierTranslator;

	private final Collection<Term> m_Axioms;

	private IUltimateServiceProvider mServices;

	public Boogie2SMT(Script script, BoogieDeclarations boogieDeclarations, boolean blackHoleArrays,
			IUltimateServiceProvider services) {
		mServices = services;
		m_BlackHoleArrays = blackHoleArrays;
		m_BoogieDeclarations = boogieDeclarations;
		m_Script = script;
		m_VariableManager = new VariableManager(m_Script);

		m_TypeSortTranslator = new TypeSortTranslator(boogieDeclarations.getTypeDeclarations(), m_Script,
				m_BlackHoleArrays, mServices);
		m_Boogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, m_Script, m_TypeSortTranslator);

		m_ConstOnlyIdentifierTranslator = new ConstOnlyIdentifierTranslator();

		m_Axioms = new ArrayList<Term>(boogieDeclarations.getAxioms().size());
		for (Axiom decl : boogieDeclarations.getAxioms()) {
			Term term = this.declareAxiom(decl);
			m_Axioms.add(term);
		}
		m_Statements2TransFormula = new Statements2TransFormula(this, mServices);
		m_Term2Expression = new Term2Expression(m_TypeSortTranslator, m_Boogie2SmtSymbolTable);

	}

	public VariableManager getVariableManager() {
		return m_VariableManager;
	}

	public Script getScript() {
		return m_Script;
	}

	public Term2Expression getTerm2Expression() {
		return m_Term2Expression;
	}

	static String quoteId(String id) {
		// return Term.quoteId(id);
		return id;
	}

	public Boogie2SmtSymbolTable getBoogie2SmtSymbolTable() {
		return m_Boogie2SmtSymbolTable;
	}

	public Statements2TransFormula getStatements2TransFormula() {
		return m_Statements2TransFormula;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return m_BoogieDeclarations;
	}

	public TypeSortTranslator getTypeSortTranslator() {
		return m_TypeSortTranslator;
	}

	ConstOnlyIdentifierTranslator getConstOnlyIdentifierTranslator() {
		return m_ConstOnlyIdentifierTranslator;
	}

	public Collection<Term> getAxioms() {
		return m_Axioms;
	}

	private Term declareAxiom(Axiom ax) {
		IdentifierTranslator[] its = new IdentifierTranslator[] { getConstOnlyIdentifierTranslator() };
		Term term = (new Expression2Term(mServices, its, m_Script, m_TypeSortTranslator, ax.getFormula())).getTerm();
		m_Script.assertTerm(term);
		return term;
	}

	public static void reportUnsupportedSyntax(BoogieASTNode BoogieASTNode, String longDescription,
			IUltimateServiceProvider services) {
		UnsupportedSyntaxResult<BoogieASTNode> result = new UnsupportedSyntaxResult<BoogieASTNode>(BoogieASTNode,
				Activator.s_PLUGIN_NAME, services.getBacktranslationService().getTranslatorSequence(), longDescription);
		services.getResultService().reportResult(Activator.s_PLUGIN_NAME, result);
		services.getProgressMonitorService().cancelToolchain();
	}

	/**
	 * Use with caution! Construct auxiliary variables only if you need then in
	 * the whole verification process. Construct auxiliary variables only if the
	 * assertion stack of the script is at the lowest level. Auxiliary variables
	 * are not supported in any backtranslation.
	 */
	public BoogieNonOldVar constructAuxiliaryGlobalBoogieVar(String identifier, String procedure, IType iType,
			BoogieASTNode BoogieASTNode) {

		return m_Boogie2SmtSymbolTable.constructAuxiliaryGlobalBoogieVar(identifier, procedure, iType,
				BoogieASTNode);
	}

	class ConstOnlyIdentifierTranslator implements IdentifierTranslator {

		@Override
		public Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			if (declInfo.getStorageClass() != StorageClass.GLOBAL) {
				throw new AssertionError();
			}
			Term result = m_Boogie2SmtSymbolTable.getBoogieConst(id).getSmtConstant();
			if (result == null) {
				throw new AssertionError();
			}
			return result;
		}
	}
}