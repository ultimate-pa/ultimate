package local.stalin.SMTInterface.groundify;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.SMTInterface.Z3Interpolator;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.FormulaWalker.SymbolVisitor;
import local.stalin.nativez3.Z3ProofRule;
import local.stalin.smt.hack.Instantiation;
import local.stalin.smt.hack.SymbolRange;

public class InstantiationFinder implements SymbolVisitor {
	private class SkolemDetector implements SymbolVisitor {
		private int numqfs = 0;
		@Override
		public void done(Term input) {}
		@Override
		public void done(PredicateAtom pa) {}

		@Override
		public void endscope(TermVariable tv) {}

		@Override
		public void endscopes(TermVariable[] tvs) {
			--numqfs;
		}
		@Override
		public void let(TermVariable tv, Term mval) {}

		@Override
		public Formula predicate(PredicateAtom pa) {
			if (numqfs == 0) {
				String pname = pa.getPredicate().getName();
	            if (pname.startsWith("quant")) {
	                // Quantifier marker detected!!!
	                int qnum = Integer.parseInt(pname.substring("quant".length()));
	                QFRange qfr = mallocnums.get(qnum);
	                if (qfr == null)
	                	throw new AssertionError("Did not find quantified formula #" + qnum);
	                if (skolems.containsKey(qfr.qf))
	                	return pa;
	                TermVariable[] tvs = qfr.qf.getVariables();
	                Term[] args = pa.getParameters();
	                Map<TermVariable,Term> skolemMap = new HashMap<TermVariable, Term>(tvs.length);
	                // Dependencies: Get TermVariables to regenerate appropriate skolemization term
	                // Unfortunately, TermVariables are disambiguated...
	                Term[] depvararray = null;
	                if (args.length > tvs.length) {
	                	ArrayList<TermVariable> depvars = new ArrayList<TermVariable>();
	                	for (int i = tvs.length; i < args.length;) {
	                		int depqid = ((NumeralTerm)args[i]).getNumeral().intValue();
	                		QFRange deprange = mallocnums.get(depqid);
	                		if (deprange == null) throw new AssertionError("Did not find dependent quantifier #" + depqid);
	                		TermVariable[] adepvars = deprange.qf.getVariables();
	                		for (TermVariable tv : adepvars)
	                			depvars.add(tv);
	                		i += adepvars.length + 1;
	                	}
	                	depvararray = new Term[depvars.size()];
	                	int dest = 0;
	                	for (TermVariable tv : depvars)
	                		depvararray[dest++] = mtheory.term(tv);
	                }
	                for (int i = 0; i < tvs.length; ++i) {
	                	ApplicationTerm at = (ApplicationTerm)args[i];
	                	mrm.skolemFunction(at.getFunction(),qfr.assnum);
	                	Term skolem = depvararray == null ? at : mtheory.term(at.getFunction(), depvararray);
	                	skolemMap.put(tvs[i],skolem);
	                }
	                skolems.put(qfr.qf, skolemMap);
	            }
			}
			return pa;
		}
		@Override
		public void quantifier(TermVariable[] tvs) {
			++numqfs;
		}
		@Override
		public Term term(Term input) {
			return input;
		}
		@Override
		public boolean unflet() {
			return false;
		}
		@Override
		public boolean unlet() {
			return false;
		}
	}
	private int mnumquants = 0;
	private HashSet<Formula> seen  = new HashSet<Formula>();
	private Map<Integer,QFRange> mallocnums;
	private Map<QuantifiedFormula,Map<TermVariable,Term>> skolems;
	private Map<QuantifiedFormula,Set<Instantiation>> instances;
	private RangeMap mrm;
	private Theory mtheory;
	private Map<TermVariable,SymbolRange> mlocals;
	private Map<EqualsAtom,SymbolRange> mauxeqs;
	private Map<TermVariable,Set<TermVariable>> mdeps;
	private Set<TermVariable> mcurdeps;
	
	public InstantiationFinder(Theory theory,Map<Integer,QFRange> allocnums,
			RangeMap rm,Map<EqualsAtom,SymbolRange> auxeqs) {
		mtheory = theory;
		mallocnums = allocnums;
		mrm = rm;
		skolems = new HashMap<QuantifiedFormula, Map<TermVariable,Term>>();
		instances = new HashMap<QuantifiedFormula, Set<Instantiation>>();
		mlocals = new HashMap<TermVariable, SymbolRange>();
		mauxeqs = auxeqs;
		mdeps = new HashMap<TermVariable, Set<TermVariable>>();
		mcurdeps = new HashSet<TermVariable>();
	}
	@Override
	public void done(Term input) {}
	@Override
	public void done(PredicateAtom pa) {}
	@Override
	public void endscope(TermVariable tv) {}
	@Override
	public void endscopes(TermVariable[] tvs) {
		--mnumquants;
	}
	@Override
	public void let(TermVariable tv, Term mval) {}
	@Override
	public Formula predicate(PredicateAtom pa) {
		if (mnumquants == 0) {
			String pname = pa.getPredicate().getName();
            if (pname.startsWith("quant")) {
                // Quantifier marker detected!!!
                int qnum = Integer.parseInt(pname.substring("quant".length()));
                QFRange qfr = mallocnums.get(qnum);
                if (qfr == null)
                	throw new AssertionError("Did not find quantified formula #" + qnum);
                Term[] args = pa.getParameters();
                TermVariable[] tvs = qfr.qf.getVariables();
                // Dependencies
                Instantiation lastdepinst = null;
                if (args.length >= qfr.qf.getVariables().length) {
                	for (int i = tvs.length; i < args.length; ++i) {
                		int depqid = ((NumeralTerm)args[i++]).getNumeral().intValue();
                        QFRange deprange = mallocnums.get(depqid);
                        if( deprange == null )
                        	throw new AssertionError("Did not find depended quantified formula #" + depqid);
                        TermVariable[] depvars = deprange.qf.getVariables();
                        TermVariable tv = depvars[0];
                        if (isSkolem(deprange,tv,args[i])) {
                        	i += deprange.qf.getVariables().length;
                        } else {
                        	Map<TermVariable,Term> inst = new HashMap<TermVariable,Term>(depvars.length);
                        	for (int j = 0; j < depvars.length; ++j,++i) {
                        		inst.put(depvars[j], args[i]);
                        	}
                        	lastdepinst = getCreateChild(inst, lastdepinst, deprange);
                        }
                	}
                }// End of dependencies
                Map<TermVariable,Term> inst = new HashMap<TermVariable,Term>(tvs.length);
                for (int i = 0; i < tvs.length; ++i) {
                	inst.put(tvs[i],args[i]);
                }
                getCreateChild(inst, lastdepinst, qfr);
            }
		}
		return pa;
	}
	@Override
	public void quantifier(TermVariable[] tvs) {
		++mnumquants;
	}
	@Override
	public Term term(Term input) {
		return input;
	}
	@Override
	public boolean unflet() {
		return false;
	}
	@Override
	public boolean unlet() {
		return false;
	}
	public Map<QuantifiedFormula,Map<TermVariable,Term>> findSkolemizations(Z3ProofRule pr) {
		seen.clear();
		skolems.clear();
		SkolemDetector sd = new SkolemDetector();
		FormulaWalker fw = new FormulaWalker(sd,mtheory);
		walkProofTree(pr, fw, Z3Interpolator.PR_SKOLEMIZE);
		return skolems;
	}
	public Map<QuantifiedFormula,Map<TermVariable,Term>> findSkolemizations(Set<Formula> skolemforms) {
		seen.clear();
		skolems.clear();
		SkolemDetector sd = new SkolemDetector();
		FormulaWalker fw = new FormulaWalker(sd,mtheory);
		for (Formula sk : skolemforms)
			fw.process(sk);
		return skolems;
	}
	public Map<QuantifiedFormula,Set<Instantiation>> findInstances(Z3ProofRule pr) {
		seen.clear();
		instances.clear();
		FormulaWalker fw = new FormulaWalker(this,mtheory);
		walkProofTree(pr, fw, Z3Interpolator.PR_QUANT_INST);
		return instances;
	}
	public Map<QuantifiedFormula,Set<Instantiation>> findInstances(Set<Formula> instforms) {
		seen.clear();
		instances.clear();
		FormulaWalker fw = new FormulaWalker(this,mtheory);
		for (Formula inst : instforms)
			fw.process(inst);
		return instances;
	}
	private final void walkProofTree(Z3ProofRule pr,FormulaWalker fw,int rulenum) {
        if( pr.getRuleNumber() == rulenum ) {
//              System.err.println("Processing " + pr);
                // result one of (or (not (forall... )) (inst)) (~ (exists...) (skolem))
                Formula f = ((ConnectedFormula)pr.getResult()).getRhs();
                if (!seen.contains(f)) {
                        seen.add(f);
                        fw.process(f);
                }
        }
        Z3ProofRule[] antecedents = pr.getAntecedents();
        for( Z3ProofRule ant : antecedents )
                walkProofTree(ant,fw,rulenum);
	}
	private boolean isSkolem(QFRange deprange,TermVariable tv,Term inst) {
		Map<TermVariable,Term> skolem = skolems.get(deprange.qf);
		if (skolem != null && inst instanceof ApplicationTerm) {
			Term sinst = skolem.get(tv);
			return ((ApplicationTerm)sinst).getFunction() == ((ApplicationTerm)inst).getFunction();
		}
		return false;
	}
	private Instantiation getCreateChild(Map<TermVariable,Term> rinst,Instantiation parent,QFRange qf) {
		if (parent == null) {
			Set<Instantiation> knowninsts = instances.get(qf.qf);
			if (knowninsts == null) {
				knowninsts = new HashSet<Instantiation>();
				instances.put(qf.qf,knowninsts);
			}
			for (Instantiation cinst : knowninsts) {
				if (cinst.matches(rinst))
					return cinst;
			}
			Map<TermVariable,Term> insts = new HashMap<TermVariable, Term>(rinst.size());
			populateInstMaps(rinst, insts, qf);
			Instantiation ninst = new Instantiation(rinst,insts);
			knowninsts.add(ninst);
			return ninst;
		}
		Instantiation child = parent.getMatchingChild(rinst,qf.qf);
		if (child == null) {
			Map<TermVariable,Term> insts = new HashMap<TermVariable, Term>(rinst.size());
			populateInstMaps(rinst, insts, qf);
			child = new Instantiation(rinst,insts);
			parent.addChild(qf.qf,child);
			Set<Instantiation> knowninsts = instances.get(qf.qf);
			if (knowninsts == null) {
				knowninsts = new HashSet<Instantiation>();
				instances.put(qf.qf,knowninsts);
			}
			knowninsts.add(child);
		}
		return child;
	}
	private void populateInstMaps(Map<TermVariable,Term> rinst,Map<TermVariable,Term> insts,QFRange qf) {
		for (Map.Entry<TermVariable,Term> me : rinst.entrySet()) {
			insts.put(me.getKey(), purify(me.getValue(),qf.assnum));
		}
	}
	private Term purify(Term input,int partition) {
		if (input instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm)input;
			Term[] args = at.getParameters();
			SymbolRange funcRange = mrm.range(at.getFunction());
			if (funcRange == null)
				funcRange = SymbolRange.THEORYEXTENSION;
			boolean constant = args == null || args.length == 0;
			if (funcRange.first <= partition) {
				// in A
				if (partition <= funcRange.last) {
					// also in B
					if (constant)
						return input;
					Term[] nargs = new Term[args.length];
					for (int i = 0; i < args.length; ++i)
						nargs[i] = purify(args[i],partition);
					return mtheory.term(at.getFunction(),nargs);
				}
				// A-local
				return partitionpurify(input, Boolean.TRUE, args, constant,
						funcRange, at);
			} else {
				// B-local
				return partitionpurify(input, Boolean.FALSE, args, constant,
						funcRange, at);
			}
		} else if (input instanceof ITETerm) {
			ITETerm ite = (ITETerm)input;
			return mtheory.ite(ite.getCondition(), purify(ite.getTrueCase(),partition), purify(ite.getFalseCase(),partition));
		}
		return input;
	}
	private Term partitionpurify(Term input,Boolean partition,Term[] args,
			boolean constant,SymbolRange funcRange,ApplicationTerm at) {
		TermVariable resvar = createVarForTerm(input);
		mlocals.put(resvar, funcRange);
		if (!mcurdeps.isEmpty())
			mdeps.put(resvar, new HashSet<TermVariable>(mcurdeps));
		Term purified = input;
		if (!constant) {
			boolean added = mcurdeps.add(resvar);
			assert added : "Strange variable dependencies!";
			try {
				Term[] nargs = new Term[args.length];
				for (int i = 0; i < args.length; ++i)
					nargs[i] = purify(args[i],funcRange.last);
				purified = mtheory.term(at.getFunction(),nargs);
			} finally {
				mcurdeps.remove(resvar);
			}
		}
		mauxeqs.put((EqualsAtom)mtheory.equals(mtheory.term(resvar),purified), funcRange);
		return mtheory.term(resvar);
	}
	
	private HashMap<Term,TermVariable> instVarCache = new HashMap<Term,TermVariable>();
	private int numInsts = 0;
    TermVariable createInstVarForTerm(TermVariable oldtv,Term term) {
    	TermVariable res = instVarCache.get(term);
    	if (res == null) {
    		res = mtheory.createTermVariable(oldtv.getName()+"_"+numInsts++,oldtv.getSort());
    		instVarCache.put(term,res);
    	}
    	return res;
    }
    TermVariable createVarForTerm(Term term) {
    	TermVariable res = instVarCache.get(term);
    	if (res == null) {
    		res = mtheory.createFreshTermVariable("ipure", term.getSort());
    		instVarCache.put(term,res);
    	}
    	return res;
    }
    public Map<TermVariable,SymbolRange> getLocalityMap() {
    	return mlocals;
    }
    public Map<TermVariable,Set<TermVariable>> getOrderMap() {
    	return mdeps;
    }
}