/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * An object of this class allows one to construct a {@link TransFormula}.
 * {@link TransFormula}s are unmodifiable and have a package-private 
 * constructor. This class allows to collect data for a TransFormula and to
 * construct it.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class TransFormulaBuilder {
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final Map<TermVariable, Term> mAuxVars;
	private final Set<TermVariable> mBranchEncoders;
	private Infeasibility mInfeasibility = null;
	private Term mFormula = null;
	private final boolean mConstructionFinished = false;
	

	public TransFormulaBuilder(final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars,
			final boolean emptyAuxVars, final Map<TermVariable, Term> auxVars,
			final boolean emptyBranchEncoders, final Set<TermVariable> branchEncoders) {
		super();
		if (inVars == null) {
			mInVars = new HashMap<>();
		} else {
			mInVars = new HashMap<>(inVars);
		}
		if (outVars == null) {
			mOutVars = new HashMap<>();
		} else {
			mOutVars = new HashMap<>(outVars);
		}
		if (emptyAuxVars) {
			mAuxVars = Collections.emptyMap();
			if (auxVars != null) {
				throw new IllegalArgumentException("if emptyAuxVars=true, you cannot provide aux vars");
			}
		} else {
			if (auxVars == null) {
				mAuxVars = new HashMap<>();
			} else {
				mAuxVars = new HashMap<>(auxVars);
			}
		}
		if (emptyBranchEncoders) {
			mBranchEncoders = Collections.emptySet();
			if (branchEncoders != null) {
				throw new IllegalArgumentException("if emptyBranchEncoders=true, you cannot provide branchEncoders");
			}
		} else {
			if (branchEncoders == null) {
				mBranchEncoders = new HashSet<>();
			} else {
				mBranchEncoders = new HashSet<>(branchEncoders);
			}
		}
	}
	
	public Term addAuxVar(final TermVariable arg0, final Term arg1) {
		if (mConstructionFinished) {
			return mAuxVars.put(arg0, arg1);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public void addAuxVars(final Map<? extends TermVariable, ? extends Term> arg0) {
		if (mConstructionFinished) {
			mAuxVars.putAll(arg0);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public Term removeAuxVar(final TermVariable arg0) {
		if (mConstructionFinished) {
			return mAuxVars.remove(arg0);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public boolean addBranchEncoder(final TermVariable arg0) {
		if (mConstructionFinished) {
			return mBranchEncoders.add(arg0);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public boolean addBranchEncoders(final Collection<? extends TermVariable> arg0) {
		if (mConstructionFinished) {
			return mBranchEncoders.addAll(arg0);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public TermVariable addInVar(final IProgramVar key, final TermVariable value) {
		if (mConstructionFinished) {
			return mInVars.put(key, value);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public void addInVars(final Map<? extends IProgramVar, ? extends TermVariable> m) {
		if (mConstructionFinished) {
			mInVars.putAll(m);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public TermVariable removeInVar(final IProgramVar key) {
		if (mConstructionFinished) {
			return mInVars.remove(key);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public TermVariable addOutVar(final IProgramVar key, final TermVariable value) {
		if (mConstructionFinished) {
			return mOutVars.put(key, value);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public void addOutVars(final Map<? extends IProgramVar, ? extends TermVariable> m) {
		if (mConstructionFinished) {
			mOutVars.putAll(m);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public TermVariable removeOutVar(final IProgramVar key) {
		if (mConstructionFinished) {
			return mOutVars.remove(key);
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public void setInfeasibility(final Infeasibility infeasibility) {
		if (mConstructionFinished) {
			if (mInfeasibility == null) {
				mInfeasibility = infeasibility;
			} else {
				throw new IllegalStateException("Infeasibility already set.");
			}
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}

	public void setFormula(final Term formula) {
		if (mConstructionFinished) {
			if (mFormula == null) {
				mFormula = formula;
			} else {
				throw new IllegalStateException("Formula already set.");
			}
		} else {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
	}
	
	public TransFormula finishConstruction(final Script script) {
		return new TransFormula(mFormula, mInVars, mOutVars, mAuxVars, mBranchEncoders, mInfeasibility, script);
	}
}
