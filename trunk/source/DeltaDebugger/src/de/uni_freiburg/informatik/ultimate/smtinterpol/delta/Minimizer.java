package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.delta.TermSimplifier.Mode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class Minimizer {
	
	private static class OutputReaper extends Thread implements Runnable {

		private InputStream m_ToReap;
		
		public OutputReaper(InputStream toReap) {
			m_ToReap = toReap;
			setDaemon(true);
		}
		
		@Override
		public void run() {
			byte[] chunk = new byte[1024];
			try {
				while (m_ToReap.read(chunk) != -1) ;
			} catch (IOException ignored) {}
			System.err.println("OutputReaper terminating");
			
		}
		
	}
	
	private static class DeactivateCmds implements BinSearch.Driver<Cmd> {

		@Override
		public void prepare(List<Cmd> sublist) {
			System.err.println("Trying " + sublist);
			for (Cmd cmd : sublist)
				cmd.deactivate();
		}

		@Override
		public void failure(List<Cmd> sublist) {
			for (Cmd cmd : sublist)
				cmd.activate();
		}

		@Override
		public void success(List<Cmd> sublist) {}
		
	}
	
	private static class SimplifyTerms implements BinSearch.Driver<Substitution> {

		private AbstractOneTermCmd m_Cmd;
		private SubstitutionManager m_Mgr;
		private List<Substitution> m_Substs;
		private List<Cmd> m_Pres;
		
		public SimplifyTerms(AbstractOneTermCmd cmd, SubstitutionManager mgr,
				List<Substitution> substs) {
			m_Cmd = cmd;
			m_Mgr = mgr;
			m_Substs = substs;
		}
		
		@Override
		public void prepare(List<Substitution> sublist) {
			SubstitutionApplier applier = new SubstitutionApplier();
			for (Substitution subst : sublist)
				subst.activate();
			System.err.println("Active substs: " + sublist); 	
			applier.init(m_Mgr.getDepth(), m_Substs);
			Term simp = applier.apply(m_Cmd.getTerm());
			System.err.println("simp = " + simp);
			m_Cmd.setTerm(simp);
			m_Pres = applier.getAdds();
			m_Cmd.appendPreCmds(m_Pres);
		}

		@Override
		public void failure(List<Substitution> sublist) {
			m_Cmd.removePreCmds(m_Pres);
			m_Cmd.failure();
			for (Substitution subst : sublist)
				subst.deactivate();
			m_Pres = null;
		}

		@Override
		public void success(List<Substitution> sublist) {
			for (Substitution s : sublist)
				s.success();
			m_Cmd.success();
			m_Pres = null;
		}
		
	}
	
	private static class RemoveTrueParts implements BinSearch.Driver<Term> {

		private GetInterpolants m_Gi;
		
		public RemoveTrueParts(GetInterpolants gi) {
			m_Gi = gi;
		}
		
		@Override
		public void prepare(List<Term> sublist) {
			Minimizer.removeParts(m_Gi, sublist);
		}

		@Override
		public void failure(List<Term> sublist) {
			m_Gi.failure();
		}

		@Override
		public void success(List<Term> sublist) {
			m_Gi.success();
		}
		
	}
	
	private static class RemoveScopes implements BinSearch.Driver<Scope> {
		
		private List<Cmd> m_Cmds;
		
		public RemoveScopes(List<Cmd> cmds) {
			m_Cmds = cmds;
		}

		@Override
		public void prepare(List<Scope> sublist) {
			for (Scope s : sublist) {
				for (int i = s.first; i < s.last; ++i)
					m_Cmds.get(i).deactivate();
				ScopeCmd sc = (ScopeCmd) m_Cmds.get(s.last);
				int remScopes = sc.getNumScopes() - s.reduce;
				if (remScopes == 0)
					sc.deactivate();
				else
					sc.tryNumScopes(remScopes);
			}
		}

		@Override
		public void failure(List<Scope> sublist) {
			for (Scope s : sublist) {
				for (int i = s.first; i < s.last; ++i)
					m_Cmds.get(i).activate();
				ScopeCmd sc = (ScopeCmd) m_Cmds.get(s.last);
				if (sc.isActive())
					sc.reset();
				else
					sc.activate();
			}
		}

		@Override
		public void success(List<Scope> sublist) {
			for (Scope s : sublist)
				s.deactivated = true;
		}
		
	}
	
	private List<Cmd> m_Cmds;
	private int m_GoldenExit;
	private File m_TmpFile, m_ResultFile;
	private String m_Solver;
	
	private int m_TestCtr = 0, m_SuccTestCtr = 0;
	
	public Minimizer(List<Cmd> cmds, int goldenExit,
			File tmpFile, File resultFile, String solver) {
		m_Cmds = cmds;
		m_GoldenExit = goldenExit;
		m_TmpFile = tmpFile;
		m_ResultFile = resultFile;
		m_Solver = solver;
	}
	
	public boolean deltaDebug() throws IOException, InterruptedException {
		System.err.println("# commands: " + m_Cmds.size());
		int numRounds = 0;
		boolean scopes, cmds, terms, bindings, neutrals, lists, ips, decls;
		do {
			// TODO removeScopes multiple times makes no sense...
			scopes = true && removeScopes();
			cmds = true && removeCmds();
			shrinkCmdList();
			terms = true && simplifyTerms();
			bindings = true && removeBindings();
			neutrals = true && removeNeutrals();
			lists = true && simplifyTermListCmds();
			ips = true && simplifyGetInterpolants();
			decls = true && removeDecls();
			// Not needed anymore since I don't do further tests...
	//		shrinkCmdList();
			++numRounds;
		} while (scopes || cmds || terms || bindings || neutrals || lists || ips || decls);
		boolean features = removeFeatures();
		System.err.println("# tests: " + m_TestCtr);
		System.err.println("# successful tests: " + m_SuccTestCtr);
		System.err.println("# rounds: " + numRounds);
		return numRounds > 1 || features;
//		return scopes || cmds || terms || bindings || neutrals || lists || ips || decls;
	}
	
	private static class Scope {
		int first;
		int last;
		int reduce;
		List<Scope> nested;
		boolean deactivated = false;
		public Scope(int f) {
			first = f;
		}
		public void nest(Scope s) {
			if (nested == null)
				nested = new ArrayList<Scope>();
			nested.add(s);
		}
	}
	
	private List<Scope> detectScopes() {
		ArrayDeque<Scope> ppStack = new ArrayDeque<Scope>();
		// All toplevel scopes.
		List<Scope> res = new ArrayList<Scope>();
		for (int i = 0; i < m_Cmds.size(); ++i) {
			Cmd cmd = m_Cmds.get(i);
			if (!cmd.isActive())
				continue;
			if (cmd instanceof ScopeCmd) {
				ScopeCmd sc = (ScopeCmd) cmd;
				if (sc.isScopeStart()) {
					System.err.println("Found scope start at " + i);
					Scope s = new Scope(i);
					for (int n = 0; n < sc.getNumScopes(); ++n)
						ppStack.push(s);
				} else {
					System.err.println("Found scope end at " + i);
					for (int n = 0; n < sc.getNumScopes(); ++n) {
						Scope last = ppStack.pop();
						Scope next = ppStack.peek();
						// We have found a scope end...
						last.last = i;
						last.reduce = n + 1;
						if (next == null)
							// toplevel scope
							res.add(last);
						else if (last != next)
							next.nest(last);
					}
				}
			}
		}
		return res;
	}
	
	private boolean removeScopes() throws IOException, InterruptedException {
		System.err.println("Removing scopes...");
		boolean res = false;
		ArrayDeque<List<Scope>> todo = new ArrayDeque<List<Scope>>();
		todo.push(detectScopes());
		while (!todo.isEmpty()) {
			List<Scope> scopes = todo.pop();
			BinSearch<Scope> bs = new BinSearch<Scope>(
					scopes, new RemoveScopes(m_Cmds));
			res |= bs.run(this);
			for (Scope s : scopes)
				if (!s.deactivated && s.nested != null)
					todo.push(s.nested);
		}
		System.err.println("...done");
		return res;
	}
	
	private boolean removeScopesOld() throws IOException, InterruptedException {
		boolean res = false;
		for (int i = 0; i < m_Cmds.size(); ++i) {
			Cmd cmd = m_Cmds.get(i);
			if (!cmd.isActive())
				continue;
			if (cmd instanceof ScopeCmd) {
				ScopeCmd sc = (ScopeCmd) cmd;
				if (sc.isScopeStart()) {
					System.err.println("Found scope start at " + i);
					// Try to remove this scope
					int numScopes = sc.getNumScopes();
					cmd.deactivate();
					int j = i+1;
					for ( ; j < m_Cmds.size() && numScopes > 0; ++j) {
						Cmd cmdj = m_Cmds.get(j);
						cmdj.deactivate();
						if (cmdj instanceof ScopeCmd) {
							ScopeCmd scj = (ScopeCmd) cmdj;
							if (scj.isScopeStart())
								numScopes += scj.getNumScopes();
							else
								numScopes -= scj.getNumScopes();
						}
					}
					System.err.println("Corresponding scope end at " + (j-1));
					if (numScopes < 0) {
						/* Only the last pop can remove more levels than
						 * present.  We can simply reduce that number.
						 * pop command is at j-1.
						 */
						ScopeCmd lastpop = (ScopeCmd) m_Cmds.get(--j);
						lastpop.activate();
						lastpop.tryNumScopes(lastpop.getNumScopes() + numScopes);
					}
					if (test()) {
						// We deactivated up to (not including) j
						// But i will be incremented at the end of the for-i loop
						i = j - 1;
						res = true;
					} else {
						// Error could not be reproduced => backtrack
						if (numScopes < 0)
							((ScopeCmd) m_Cmds.get(j)).reset();
						for (int k = i; k < j; ++k)
							m_Cmds.get(k).activate();
					}
				}
			}
		}
		return res;
	}
	
	private boolean removeCmds() throws IOException, InterruptedException {
		System.err.println("Removing commands...");
		List<Cmd> cmds = new ArrayList<Cmd>();
		for (int i = 0; i < m_Cmds.size(); ++i) {
			Cmd cmd = m_Cmds.get(i);
			if (!cmd.isActive())
				continue;
			if (cmd.canBeRemoved() && !cmd.hasDefinitions()) {
				cmds.add(cmd);
			}
		}
		boolean res = deactivateCmds(cmds);
		System.err.println("...done");
		return res;
	}
	
	private boolean deactivateCmds(List<Cmd> toDeactivate) throws IOException, InterruptedException {
		DeactivateCmds driver = new DeactivateCmds();
		BinSearch<Cmd> bs = new BinSearch<Cmd>(toDeactivate, driver);
		return bs.run(this);
	}
	
	private boolean removeDecls() throws IOException, InterruptedException {
		System.err.println("Removing unused declarations...");
		// Collect used definitions
		ScopedHashMap<String, Cmd> definitions =
				new ScopedHashMap<String, Cmd>();
		Set<Cmd> usedDefs = new HashSet<Cmd>();
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive())
				continue;
			cmd.addUsedDefinitions(definitions, usedDefs);
			if (cmd.hasDefinitions())
				cmd.insertDefinitions(definitions);
			if (cmd instanceof ScopeCmd) {
				ScopeCmd scope = (ScopeCmd) cmd;
				if (scope.isScopeStart())
					for (int i = 0; i < scope.getNumScopes(); ++i)
						definitions.beginScope();
				else
					for (int i = 0; i < scope.getNumScopes(); ++i)
						definitions.endScope();
			}
		}
		// Free some space...
		definitions = null;
		// Collect unused definitions
		List<Cmd> unusedDefs = new ArrayList<Cmd>();
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive())
				continue;
			if (cmd.hasDefinitions() && !usedDefs.contains(cmd))
				unusedDefs.add(cmd);
		}
		boolean res = deactivateCmds(unusedDefs);
		// Now, we have deactivated all unused definitions that can be
		// removed completely from the input.  But unfortunately some of these
		// definitions might be :named annotations and we still need the term!
		// Try to only remove the annotation.
		for (Iterator<Cmd> it = unusedDefs.iterator(); it.hasNext(); ) {
			Cmd next = it.next();
			if (!next.isActive() || !isNamedAssert(next))
				it.remove();
		}
		BinSearch<Cmd> bs = new BinSearch<Cmd>(
				unusedDefs, new BinSearch.Driver<Cmd>() {

			@Override
			public void prepare(List<Cmd> sublist) {
				for (Cmd cmd : sublist) {
					OneTermCmd tcmd = (OneTermCmd) cmd;
					Term stripped = new TermTransformer() {

						@Override
						public void postConvertAnnotation(AnnotatedTerm old,
								Annotation[] newAnnots, Term newBody) {
							ArrayList<Annotation> noNames =
									new ArrayList<Annotation>(newAnnots.length);
							for (Annotation a : newAnnots)
								if (!a.getKey().equals(":named"))
									noNames.add(a);
							setResult(noNames.isEmpty() ? newBody : 
								old.getTheory().annotatedTerm(noNames.toArray(
										new Annotation[noNames.size()]),
										newBody));
						}
						
					}.transform(tcmd.getTerm());
					tcmd.setTerm(stripped);
				}
			}

			@Override
			public void failure(List<Cmd> sublist) {
				for (Cmd cmd : sublist)
					((OneTermCmd) cmd).failure();
			}

			@Override
			public void success(List<Cmd> sublist) {
				for (Cmd cmd : sublist)
					((OneTermCmd) cmd).success();				
			}
			
		});
		res |= bs.run(this); 
		System.err.println("...done");
		return res;
	}
	
	private boolean isUnnamedAssert(AbstractOneTermCmd cmd) {
		return (cmd instanceof OneTermCmd) && 
				((OneTermCmd) cmd).getCmd().equals("assert") &&
				!cmd.hasDefinitions();
	}
	
	private boolean isNamedAssert(Cmd cmd) {
		if (cmd instanceof OneTermCmd) {
			OneTermCmd tcmd = (OneTermCmd) cmd;
			if (tcmd.getCmd().equals("assert") &&
					tcmd.getTerm() instanceof AnnotatedTerm)
				for (Annotation a : ((AnnotatedTerm) tcmd.getTerm()).getAnnotations())
					if (a.getKey().equals(":named"))
						return true;
		}
		return false;
	}
	
	private boolean removeUnusedCore(Mode mode) throws IOException, InterruptedException {
		boolean res = false;
		TermSimplifier simp = new TermSimplifier(mode);
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd))
				continue;
			AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			Term s = simp.transform(tcmd.getTerm());
			if (s != tcmd.getTerm()) {
				tcmd.setTerm(s);
				if (test()) {
					res = true;
					tcmd.success();
				} else
					tcmd.failure();
			}
		}
		return res;
	}
	
	private boolean removeBindings() throws IOException, InterruptedException {
		return removeUnusedCore(Mode.BINDINGS);
	}
	
	private boolean removeNeutrals() throws IOException, InterruptedException {
		return removeUnusedCore(Mode.NEUTRALS);
	}
	
	private boolean simplifyTerms() throws IOException, InterruptedException {
		System.err.println("Simplifying terms...");
		boolean res = false;
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd))
				continue;
			boolean localres = false;
			AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			SubstitutionManager substmgr =
					new SubstitutionManager(tcmd);
			// Try to simplify this one command...
			if (isUnnamedAssert(tcmd))
				// We should not substitute the top level
				substmgr.deepen();
			deepen: while (substmgr.deepen()) {
				List<Substitution> substs;
				do {
					substs = substmgr.getSubstitutions();
					if (substs.isEmpty())
						continue deepen;
					System.err.println("Term: " + tcmd.getTerm());
					System.err.println("Substs: " + substs);
					SimplifyTerms driver = new SimplifyTerms(
							tcmd, substmgr, substs);
					BinSearch<Substitution> bs =
							new BinSearch<Substitution>(substs, driver);
					localres |= bs.run(this);
				} while (substmgr.failed());
			}
			res |= localres;
		}// Cmd-loop
		System.err.println("...done");
		return res;
	}
	
	private Term unfoldAnd(Term p1, Term p2) {
		ArrayList<Term> conjuncts = new ArrayList<Term>();
		ApplicationTerm at = (ApplicationTerm) p1;
		if (at.getFunction() == at.getTheory().m_And)
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		else
			conjuncts.add(p1);
		at = (ApplicationTerm) p2;
		if (at.getFunction() == at.getTheory().m_And)
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		else
			conjuncts.add(p2);
		return p1.getTheory().term("and",
				conjuncts.toArray(new Term[conjuncts.size()]));
	}
	
	private boolean mergeSequential(GetInterpolants gi) throws IOException, InterruptedException {
		boolean goon = true, res = false;
		int start = 0;
		outer: while (goon) {
			goon = false;
			Term[] partition = gi.getPartition();
			int[] sos = gi.getStartOfSubtree();
			if (sos.length == 2)
				// We cannot merge anymore!
				return res;
			for (int i = start; i < sos.length - 1; ++i) {
				if (sos[i] == sos[i+1]) {
					// Try to merge
					Term[] newPartition = new Term[partition.length - 1];
					int[] newSos = new int[sos.length - 1];
					int diff = 0;
					for (int j = 0; j < partition.length; ++j) {
						if (i == j) {
							newPartition[j] =
									unfoldAnd(partition[j], partition[j+1]);
							newSos[j] = sos[j];
							diff = 1;
							// Don't consider j+1
							++j;
						} else {
							newPartition[j - diff] = partition[j];
							newSos[j - diff] = Math.max(sos[j] - diff, 0);
						}
					}
					gi.setNewPartition(newPartition);
					gi.setNewStartOfSubtree(newSos);
					if (test()) {
						System.err.println("Successful sequential merge");
						// Store to minimized array and restart with it.
						gi.success();
						goon = true;
						res = true;
						start = i;
						continue outer;
					} else
						gi.failure();
				}
			}
		}
		return res;
	}
	
	private int numChildren(int[] sos, int parent) {
		int numChildren = 0;
		int child = parent - 1;
		while (child >= sos[parent]) {
			++numChildren;
			child = sos[child] - 1;
		}
		return numChildren;
	}
	
	private void mergeWithChild(GetInterpolants gi, int parent, int child) {
		int[] sos = gi.getStartOfSubtree();
		int childidx = parent - 1;
		for (/* Nothing */; child > 0; --child)
			childidx = sos[childidx];
		Term[] partition = gi.getPartition();
		Term[] newPartition = new Term[partition.length - 1];
		int[] newSos = new int[sos.length - 1];
		int diff = 0;
		for (int i = 0; i < partition.length; ++i) {
			if (i == childidx) {
				diff = 1;
			} else if (i == parent) {
				newPartition[i - diff] =
						unfoldAnd(partition[childidx], partition[parent]);
				newSos[i - diff] = Math.max(sos[i] - 1, 0);
			} else {
				newPartition[i - diff] = partition[i];
				newSos[i - diff] = Math.max(sos[i] - 1, 0);
			}
		}
	}
	
	private boolean mergeTree(GetInterpolants gi) throws IOException, InterruptedException {
		boolean res = false;
		int[] sos = gi.getStartOfSubtree();
		int n = sos.length;
		for (int i = 1; i < n; ++i) {
			//@ invariant n == gi.getPartition().length && 0<= i <= n
			// invariant n >= 2 is hidden in assumption about interpolation tree
			int children = numChildren(sos, i);
			for (int child = 0; child < children; /*Nothing*/) {
				//@ invariant 0 <= child <= children
				//@ invariant old(children) >= children
				//@ invariant n == gi.getPartition().length
				//@ invariant i <= n
				// invariant n >= 2 see above
				if (n == 2)
					// No further merge possible!
					return res;
				mergeWithChild(gi, i, child);
				if (test()) {
					res = true;
					gi.success();
					--i;
					--n;
					--children;
				} else {
					gi.failure();
					++child;
				}
			}
		}
		return res;
	}
	
	private boolean isAnd(Term t) {
		return ((ApplicationTerm) t).getFunction() == t.getTheory().m_And;
	}
	
	private boolean simplifyInterpolantPartitions(GetInterpolants gi) throws IOException, InterruptedException {
		boolean res = false;
		Term[] partition = gi.getPartition();
		if (partition.length == 2)
			return false;
		int i = 0;
		while (i < partition.length) {
			// Try to remove partition i
			// 1. complete
			int newlength = partition.length - 1;
			if (newlength < 2)
				// We cannot remove anything anymore!!!
				return res;
			Term[] newPartition = new Term[newlength];
			int[] newSos = new int[newlength];
			int[] sos = gi.getStartOfSubtree();
			int diff = 0;
			for (int j = 0; j < partition.length; ++j) {
				if (j == i) {
					diff = 1;
				} else {
					newPartition[j - diff] = partition[j];
					newSos[j - diff] = Math.max(0, sos[j] - diff);
				}
			}
			gi.setNewPartition(newPartition);
			gi.setNewStartOfSubtree(newSos);
			if (test()) {
				gi.success();
				partition = newPartition;
				res = true;
				// Don't increment i since we shifted a new element here
			} else {
				gi.failure();
				// 2. If conjunctive partition, try to simplify conjunction
				if (isAnd(partition[i])) {
					Term[] conjs =
							((ApplicationTerm) partition[i]).getParameters();
					ArrayList<Term> newcs =
							new ArrayList<Term>(conjs.length - 1);
					int c = 0;
					while (c < conjs.length) {
						for (int j = 0; j < conjs.length; ++j)
							if (j != c)
								newcs.add(conjs[j]);
						newPartition = partition.clone();
						newPartition[i] = buildAnd(newcs);
						gi.setNewPartition(newPartition);
						if (test()) {
							gi.success();
							conjs = ((ApplicationTerm) newPartition[i]).
									getParameters();
							partition = newPartition;
							res = true;
							// Don't increment c since we shifted elements
						} else {
							gi.failure();
							++c;
						}
					}
				}
				++i;
			}
		}
		return res;
	}
	
	private static ApplicationTerm buildAnd(List<Term> conjs) {
		if (conjs.isEmpty())
			return null;
		if (conjs.size() == 1)
			return (ApplicationTerm) conjs.get(0);
		return conjs.get(0).getTheory().term(
				"and", conjs.toArray(new Term[conjs.size()]));
	}
	
	private static void removeParts(GetInterpolants gi, List<Term> toRemove) {
		System.err.println("Removing " + toRemove);
		int diff = 0;
		Term[] origpart = gi.getPartition();
		int[] origsos = gi.getStartOfSubtree();
		List<Term> newpart = new ArrayList<Term>(origpart.length);
		List<Integer> newsos = new ArrayList<Integer>(origsos.length);
		Iterator<Term> it = toRemove.iterator();
		Term remove = it.hasNext() ? it.next() : null;
		for (int i = 0; i < origpart.length; ++i) {
			ApplicationTerm at = (ApplicationTerm) origpart[i];
			if (at == remove) {
				++diff;
				remove = it.hasNext() ? it.next() : null;
				continue;
			}
			if (at.getFunction() == at.getTheory().m_And) {
				List<Term> newChildren = new ArrayList<Term>(
						at.getParameters().length);			
				for (Term p : at.getParameters()) {
					if (p == remove)
						remove = it.hasNext() ? it.next() : null;
					else
						newChildren.add(p);
				}
				if (newChildren.size() == 0) {
					++diff;
					continue;
				}
				if (newChildren.size() != at.getParameters().length)
					at = buildAnd(newChildren);
			}
			newpart.add(at);
			newsos.add(Math.max(0, origsos[i] - diff));
		}
		gi.setNewPartition(newpart.toArray(new Term[newpart.size()]));
		int[] newsosA = new int[newsos.size()];
		for (int i = 0; i < newsos.size(); ++i)
			newsosA[i] = newsos.get(i);
		gi.setNewStartOfSubtree(newsosA);
	}
	
	private boolean removeTruePartitions(
			GetInterpolants gi, Map<Term, Term> actualNames) throws IOException, InterruptedException {
		List<Term> trueParts = new ArrayList<Term>();
		for (Term t : gi.getPartition()) {
			ApplicationTerm at = (ApplicationTerm) t;
			// could be (and ...) or a name
			if (at.getFunction() == at.getTheory().m_And) {
				for (Term p : at.getParameters()) {
					ApplicationTerm at2 = (ApplicationTerm) p;
					if (actualNames.get(at2) ==	at2.getTheory().TRUE)
						trueParts.add(at2);
				}
			} else if (actualNames.get(at) == at.getTheory().TRUE)
				trueParts.add(at);
		}
		RemoveTrueParts driver = new RemoveTrueParts(gi);
		BinSearch<Term> bs = new BinSearch<Term>(trueParts, driver);
		return bs.run(this);
	}
	
	private boolean simplifyGetInterpolants() throws IOException, InterruptedException {
		System.err.println("Simplifying get-interpolants...");
		boolean res = false;
		Map<Term, Term> actualNames = new HashMap<Term, Term>();
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive())
				continue;
			if (cmd instanceof GetInterpolants) {
				GetInterpolants gi = (GetInterpolants) cmd;
				res |= simplifyInterpolantPartitions(gi);
				// This should be superseded by simplifyInterpolantPartitions
//				res |= removeTruePartitions(gi, actualNames);
				// This should be superseded by mergeTree
//				res |= mergeSequential(gi);
				res |= mergeTree(gi);
			} else if (isNamedAssert(cmd)) {
				AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
				AnnotatedTerm t = (AnnotatedTerm) tcmd.getTerm();
				Term v = t.getSubterm();
				for (Annotation a : t.getAnnotations())
					if (a.getKey().equals(":named"))
						actualNames.put(
								t.getTheory().term(a.getValue().toString()), v);
			}
		}
		System.err.println("...done");
		return res;
	}
	
	private boolean simplifyTermListCmds() throws IOException, InterruptedException {
		System.err.println("Simplifying term list commands...");
		List<TermListCmd> cmds = new ArrayList<TermListCmd>();
		for (Cmd cmd : m_Cmds) {
			if (!cmd.isActive())
				continue;
			if (cmd instanceof TermListCmd)
				cmds.add((TermListCmd) cmd);
		}
		if (cmds.isEmpty()) {
			System.err.println("...done");
			return false;
		}
		// Try to reduce number of terms in the list
		// First try to reduce all cmds to their lower half terms.
		boolean goon = true;
		boolean res = false;
		while (goon) {
			goon = false;
			for (TermListCmd cmd : cmds) {
				Term[] terms = cmd.getTerms();
				if (terms.length == 1)
					continue;
				goon = true;
				Term[] newTerms = new Term[terms.length / 2];
				System.arraycopy(terms, 0, newTerms, 0, newTerms.length);
				cmd.setNewTerms(newTerms);
			}
			if (!test()) {
				// We had a failure => Try to reduce to the other half
				for (TermListCmd cmd : cmds) {
					cmd.failure();
					Term[] terms = cmd.getTerms();
					if (terms.length == 1)
						continue;
					goon = true;
					int len = terms.length - terms.length / 2;
					Term[] newTerms = new Term[len];
					System.arraycopy(terms, terms.length / 2, newTerms, 0,
							newTerms.length);
					cmd.setNewTerms(newTerms);
				}
				if (!test()) {
					for (TermListCmd cmd : cmds)
						cmd.failure();
					// Both reductions failed => give up
					System.err.println("...done");
					return res;
				} else
					for (TermListCmd cmd : cmds)
						cmd.success();
			} else {
				for (TermListCmd cmd : cmds)
					cmd.success();
				res = true;
			}
		}
		System.err.println("...done");
		return res;
	}
	
	private void shrinkCmdList() {
		System.err.println("Shrinking command list...");
		for (Iterator<Cmd> it = m_Cmds.iterator(); it.hasNext(); ) {
			if (!it.next().isActive())
				it.remove();
		}
		System.err.println("...done");
	}
	
	private boolean removeFeatures() throws IOException, InterruptedException {
		Map<String, Cmd> features = new HashMap<String, Cmd>();
		for (Cmd cmd : m_Cmds)
			if (cmd.isActive()) {
				String feature = cmd.provideFeature();
				if (feature != null) {
					System.err.println("Found feature " + feature);
					features.put(feature, cmd);
				}
			}
		for (Cmd cmd : m_Cmds)
			if (cmd.isActive())
				cmd.checkFeature(features);
		List<Cmd> featureProvider = new ArrayList<Cmd>(features.values());
		System.err.println("Trying to remove features " + featureProvider);
		return deactivateCmds(featureProvider);
	}

	/**
	 * Test a modified input script for error reproduction.
	 * @return Did the error still occur?
	 * @throws IOException
	 * @throws InterruptedException
	 */
	boolean test() throws IOException, InterruptedException {
		++m_TestCtr;
		System.err.println("Dumping...");
		dumpCmds();
		System.err.println("Testing...");
		Process p = Runtime.getRuntime().exec(m_Solver);
		OutputReaper out = new OutputReaper(p.getInputStream());
		out.start();
		OutputReaper err = new OutputReaper(p.getErrorStream());
		err.start();
		int exitVal = p.waitFor();
		out.join();
		err.join();
		if (exitVal == m_GoldenExit) {
			++m_SuccTestCtr;
			System.err.println("Success");
			Files.copy(m_TmpFile.toPath(), m_ResultFile.toPath(),
					StandardCopyOption.REPLACE_EXISTING);
			return true;
		}
		System.err.println("Failure");
		return false;
	}
	
	private void dumpCmds() throws FileNotFoundException {
		PrintWriter out = new PrintWriter(m_TmpFile);
		for (Cmd cmd : m_Cmds) {
			if (cmd.isActive())
				cmd.dump(out);
		}
		out.flush();
		out.close();
	}
	
	public static void usage() {
		System.err.println(
				"Usage: Minimizer <infile> <outfile> <command> <args>");
		System.err.println("where");
		System.err.println("\tinfile\tis the original input file");
		System.err.println("\toutfile\tis the desired output file");
		System.err.println("\tcommand\tis the command to start the solver");
		System.err.println("\targs\tare optional arguments to \"command\"");
		System.exit(0);
	}
	
	public static void main(String[] args) {
		if (args.length < 3)
			usage();
		String infile = args[0];
		String outfile = args[1];
		StringBuilder command = new StringBuilder();
		for (int i = 2; i < args.length; ++i)
			command.append(args[i]).append(' ');
		File resultFile = new File(outfile);
		try {
			File tmpFile = File.createTempFile("minimize", ".smt2");
			tmpFile.deleteOnExit();
			File input = new File(infile);
			Files.copy(input.toPath(), resultFile.toPath());
			Files.copy(input.toPath(), tmpFile.toPath(),
					StandardCopyOption.REPLACE_EXISTING);
			command.append(tmpFile.getAbsolutePath());
			String solver = command.toString();
			// Free space
			command = null;
			System.err.println("Starting " + solver);
			Process p = Runtime.getRuntime().exec(solver);
			OutputReaper out = new OutputReaper(p.getInputStream());
			out.start();
			OutputReaper err = new OutputReaper(p.getErrorStream());
			err.start();
			int goldenExit = p.waitFor();
			out.join();
			err.join();
			// Free space
			p = null;
			System.err.println("Got golden exit code: " + goldenExit);
			ParseScript ps = new ParseScript();
			ParseEnvironment pe = new ParseEnvironment(ps) {

				@Override
				public void printSuccess() {}

				@Override
				public void printValues(Map<Term, Term> values) {}

				@Override
				public void printResponse(Object response) {}

				@Override
				public void printInfoResponse(String info, Object response) {}

				@Override
				public void printTermResponse(Term[] response) {}
				
			};
			System.err.println("Begin parsing");
			pe.parseScript(infile);
			// Free space
			pe = null;
			System.err.println("Parsing done");
			Minimizer mini = new Minimizer(
					ps.getCmds(), goldenExit, tmpFile, resultFile, solver);
			// Free space
			ps = null;
			if (!mini.deltaDebug())
				System.err.println("Failed to minimize");
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
	
}
