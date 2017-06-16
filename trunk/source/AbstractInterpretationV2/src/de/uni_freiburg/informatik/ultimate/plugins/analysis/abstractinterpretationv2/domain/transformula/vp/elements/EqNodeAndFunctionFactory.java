package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;

public class EqNodeAndFunctionFactory {
	
	ManagedScript mMgdScript;

	
	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();


	private final Map<Term, EqFunction> mTermToEqFunction = new HashMap<>();
	
	private final VPDomainPreanalysis mPreAnalysis;
	
	public EqNodeAndFunctionFactory(VPDomainPreanalysis preAnalysis, ManagedScript script) {
		mPreAnalysis = preAnalysis;
		mMgdScript = script;
	}
	

	@Deprecated
	public EqAtomicBaseNode getOrConstructEqAtomicNode(IProgramVarOrConst varOrConst, Term substitutedTerm) {
		
		return new EqAtomicBaseNode(varOrConst, substitutedTerm, this);
	}

	@Deprecated
	public EqFunctionNode getOrConstructEqFunctionNode(EqFunction function, List<EqNode> args) {

		final List<Term> paramTerms = args.stream().map(eqNode -> eqNode.getTerm()).collect(Collectors.toList());
		mMgdScript.lock(this);
		final Term term = mMgdScript.term(this, 
				function.getFunctionName(), 
				paramTerms.toArray(new Term[paramTerms.size()]));
		mMgdScript.unlock(this);
		
		
		return  new EqFunctionNode(function, args, term, this);
	}

	public ManagedScript getScript() {
		return mMgdScript;
	}

	@Deprecated
	public EqNode getOrConstructEqNonAtomicBaseNode(Term substitutedTerm, boolean isGlobal, String procedure) {
		return new EqNonAtomicBaseNode(substitutedTerm, isGlobal, procedure, this);
	}

	@Deprecated
	public EqFunction getOrConstructEqFunction(IProgramVarOrConst pvoc) {
		return new EqFunction(pvoc, this);
	}

//	public EqFunction getOrConstructEqFunction(IProgramVarOrConst pvoc, Term term) {
//		return new EqFunction(pvoc, term, this);
//	}

	public EqNode getOrConstructEqNode(Term term) {
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0) {
			if ("select".equals(((ApplicationTerm) term).getFunction().getName())) {
				return getOrConstructEqFunctionNode((ApplicationTerm) term);
			} else if (((ApplicationTerm) term).getFunction().isIntern()) {
				return getOrConstructNonAtomicBaseNode(term);
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0) {
			return getOrConstructEqBaseNode(term);
		} else if (term instanceof TermVariable) {
			return getOrConstructEqBaseNode(term);
		} else if (term instanceof ConstantTerm) {
			return getOrConstructEqBaseNode(term);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private EqNode getOrConstructNonAtomicBaseNode(Term term) {
		// TODO Auto-generated method stub
		assert false;
		return null;
	}

	private EqNode getOrConstructEqFunctionNode(ApplicationTerm selectTerm) {
		EqNode result = mTermToEqNode.get(selectTerm);

		if (result == null) {
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(selectTerm);

			final EqFunction function = getOrConstructEqFunction(mds.getArray());
			
			final List<EqNode> args = new ArrayList<>();
			for (Term index : mds.getIndex()) {
				args.add(getOrConstructEqNode(index));
			}
			
			result = new EqFunctionNode(function, args, selectTerm, this);
			mTermToEqNode.put(selectTerm, result);
		}
		assert result instanceof EqFunctionNode;
		return result;
	}

	private EqNode getOrConstructEqBaseNode(Term term) {
		EqNode result = mTermToEqNode.get(term);
		if (result == null) {
			result = new EqAtomicBaseNode(term, this);
			mTermToEqNode.put(term, result);
		}
		assert result instanceof EqAtomicBaseNode;
		return result;
		
	}

	public EqFunction getOrConstructEqFunction(Term term) {
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0) {
			if ("store".equals(((ApplicationTerm) term).getFunction().getName())) {
				return getOrConstructEqStoreFunction((ApplicationTerm) term);
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0) {
			return getOrConstructAtomicEqFunction(term);
		} else if (term instanceof TermVariable) {
			return getOrConstructAtomicEqFunction(term);
		} else if (term instanceof ConstantTerm) {
			return getOrConstructAtomicEqFunction(term);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private EqFunction getOrConstructAtomicEqFunction(Term term) {
		assert !(term instanceof ApplicationTerm) || !"store".equals(((ApplicationTerm) term).getFunction().getName());
		EqFunction result = mTermToEqFunction.get(term);
		if (result == null) {
			result = new EqFunction(term, this);
			mTermToEqFunction.put(term, result);
		}
		assert !(result instanceof EqStoreFunction);
		return result;
	}

	private EqFunction getOrConstructEqStoreFunction(ApplicationTerm storeTerm) {
		assert "store".equals(storeTerm.getFunction().getName());
		EqFunction result = mTermToEqFunction.get(storeTerm);
		if (result == null) {
			final MultiDimensionalStore mds = new MultiDimensionalStore(storeTerm);
			
			final EqFunction function = getOrConstructEqFunction(mds.getArray());

			final List<EqNode> indices = new ArrayList<>();
			for (Term index : mds.getIndex()) {
				indices.add(getOrConstructEqNode(index));
			}

			final EqNode value = getOrConstructEqNode(mds.getValue());

			result = new EqStoreFunction(function, indices, value, storeTerm, this);
			mTermToEqFunction.put(storeTerm, result);
		}
		return result;
	}

	public EqFunction constructRenamedEqFunction(EqFunction eqFunction, Map<Term, Term> substitutionMapping) {
		final Term substitutedTerm = new Substitution(mMgdScript, substitutionMapping).transform(eqFunction.getTerm());
		return getOrConstructEqFunction(substitutedTerm);
	}

	/**
	 * 
	 * @param term
	 * @return
	 */
	public EqNode getExistingEqNode(Term term) {
		return mTermToEqNode.get(term);
	}
	
	/**
	 * 
	 * @param term
	 * @return
	 */
	public EqFunction getExistingEqFunction(Term term) {
		return mTermToEqFunction.get(term);
	}
	

}
