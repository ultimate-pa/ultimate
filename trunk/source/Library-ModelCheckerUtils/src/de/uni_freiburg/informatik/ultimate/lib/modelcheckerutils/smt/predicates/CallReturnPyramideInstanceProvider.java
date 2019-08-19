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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CallReturnPyramideInstanceProvider {

	public enum Instance {
		BEFORE_CALL, AFTER_CALL, BEFORE_RETURN, AFTER_RETURN
	}

	private final ManagedScript mMgdScript;

	private final BeforeCallCoincidingInstancesClassifier mBeforeCallCoincidingInstancesClassifier;
	private final AfterCallCoincidingInstancesClassifier mAfterCallCoincidingInstancesClassifier;
	private final BeforeReturnCoincidingInstancesClassifier mBeforeReturnCoincidingInstancesClassifier;
	private final AfterReturnCoincidingInstancesClassifier mAfterReturnCoincidingInstancesClassifier;
	private final FourWayInstanceProvider mInstanceProvider;
	private final Set<IProgramVar> mVarsAssignedOnReturn;
	private final Set<IProgramVar> mCalleeInParams;
	private final Set<IProgramNonOldVar> mModifiableGlobals;

	private final Set<TermVariable> mFreshTermVariables = new HashSet<>();

	public CallReturnPyramideInstanceProvider(final ManagedScript mgdScript,
			final Set<IProgramVar> varsAssignedOnReturn, final Set<IProgramVar> calleeInParams,
			final Set<IProgramNonOldVar> modifiableGlobals, final Instance nonAuxVarInstance) {
		super();
		mMgdScript = mgdScript;
		mVarsAssignedOnReturn = varsAssignedOnReturn;
		mCalleeInParams = calleeInParams;
		mModifiableGlobals = modifiableGlobals;
		mBeforeCallCoincidingInstancesClassifier = new BeforeCallCoincidingInstancesClassifier();
		mAfterCallCoincidingInstancesClassifier = new AfterCallCoincidingInstancesClassifier();
		mBeforeReturnCoincidingInstancesClassifier = new BeforeReturnCoincidingInstancesClassifier();
		mAfterReturnCoincidingInstancesClassifier = new AfterReturnCoincidingInstancesClassifier();
		mInstanceProvider = new FourWayInstanceProvider(nonAuxVarInstance);
	}

	public Term getInstance(final IProgramVar pv, final Instance instance) {
		switch (instance) {
		case BEFORE_CALL:
			return mInstanceProvider.getInstance(pv, mBeforeCallCoincidingInstancesClassifier.getInstances(pv));
		case AFTER_CALL:
			return mInstanceProvider.getInstance(pv, mAfterCallCoincidingInstancesClassifier.getInstances(pv));
		case BEFORE_RETURN:
			return mInstanceProvider.getInstance(pv, mBeforeReturnCoincidingInstancesClassifier.getInstances(pv));
		case AFTER_RETURN:
			return mInstanceProvider.getInstance(pv, mAfterReturnCoincidingInstancesClassifier.getInstances(pv));
		default:
			throw new AssertionError("unknown value " + instance);
		}
	}

	private class DefaultTermVariableProvider implements IValueConstruction<IProgramVar, TermVariable> {

		@Override
		public TermVariable constructValue(final IProgramVar key) {
			return key.getTermVariable();
		}
	}

	private class FreshTermVariableProvider implements IValueConstruction<IProgramVar, TermVariable> {

		private final Instance mInstance;

		public FreshTermVariableProvider(final Instance instance) {
			super();
			mInstance = instance;
		}

		@Override
		public TermVariable constructValue(final IProgramVar key) {
			final String name = key.getGloballyUniqueId() + "_" + mInstance.toString();
			final TermVariable freshTv = mMgdScript.constructFreshTermVariable(name, key.getTermVariable().getSort());
			mFreshTermVariables.add(freshTv);
			return freshTv;
		}
	}

	private abstract class CoincidingInstancesClassifier {

		public EnumSet<Instance> getInstances(final IProgramVar pv) {
			if (pv instanceof ILocalProgramVar) {
				return getInstancesLocal((ILocalProgramVar) pv);
			} else if (pv instanceof IProgramNonOldVar) {
				return getInstancesGlobalNonOld((IProgramNonOldVar) pv);
			} else if (pv instanceof IProgramOldVar) {
				return getInstancesGlobalOld((IProgramOldVar) pv);
			} else {
				throw new AssertionError("unknown kind of variable");
			}
		}

		public abstract EnumSet<Instance> getInstancesLocal(ILocalProgramVar pv);

		public abstract EnumSet<Instance> getInstancesGlobalNonOld(IProgramNonOldVar pv);

		public abstract EnumSet<Instance> getInstancesGlobalOld(IProgramOldVar pv);
	}

	private class BeforeCallCoincidingInstancesClassifier extends CoincidingInstancesClassifier {

		@Override
		public EnumSet<Instance> getInstancesLocal(final ILocalProgramVar pv) {
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.BEFORE_CALL);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalNonOld(final IProgramNonOldVar pv) {
			if (isModifiableByCallee(pv)) {
				return EnumSet.of(Instance.BEFORE_CALL);
			}
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalOld(final IProgramOldVar pv) {
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_RETURN);
		}
	}

	private class AfterCallCoincidingInstancesClassifier extends CoincidingInstancesClassifier {

		@Override
		public EnumSet<Instance> getInstancesLocal(final ILocalProgramVar pv) {
			if (inInParam(pv)) {
				return EnumSet.of(Instance.AFTER_CALL, Instance.BEFORE_RETURN);
			}
			return EnumSet.of(Instance.AFTER_CALL);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalNonOld(final IProgramNonOldVar pv) {
			if (isModifiableByCallee(pv)) {
				return EnumSet.of(Instance.AFTER_CALL);
			}
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalOld(final IProgramOldVar pv) {
			return EnumSet.of(Instance.AFTER_CALL, Instance.BEFORE_RETURN);
		}
	}

	private class BeforeReturnCoincidingInstancesClassifier extends CoincidingInstancesClassifier {

		@Override
		public EnumSet<Instance> getInstancesLocal(final ILocalProgramVar pv) {
			if (inInParam(pv)) {
				return EnumSet.of(Instance.AFTER_CALL, Instance.BEFORE_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalNonOld(final IProgramNonOldVar pv) {
			if (isModifiableByCallee(pv)) {
				if (isWrittenOnReturn(pv)) {
					return EnumSet.of(Instance.BEFORE_RETURN);
				}
				return EnumSet.of(Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
			}
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalOld(final IProgramOldVar pv) {
			return EnumSet.of(Instance.AFTER_CALL, Instance.BEFORE_RETURN);
		}
	}

	private class AfterReturnCoincidingInstancesClassifier extends CoincidingInstancesClassifier {

		@Override
		public EnumSet<Instance> getInstancesLocal(final ILocalProgramVar pv) {
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.AFTER_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalNonOld(final IProgramNonOldVar pv) {
			if (isModifiableByCallee(pv)) {
				if (isWrittenOnReturn(pv)) {
					return EnumSet.of(Instance.AFTER_RETURN);
				}
				return EnumSet.of(Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
			}
			if (isWrittenOnReturn(pv)) {
				return EnumSet.of(Instance.AFTER_RETURN);
			}
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_CALL, Instance.BEFORE_RETURN, Instance.AFTER_RETURN);
		}

		@Override
		public EnumSet<Instance> getInstancesGlobalOld(final IProgramOldVar pv) {
			return EnumSet.of(Instance.BEFORE_CALL, Instance.AFTER_RETURN);
		}
	}

	private class FourWayInstanceProvider {

		private final Instance mPriorityInstance;
		private final EnumMap<Instance, ConstructionCache<IProgramVar, TermVariable>> mInstanceProviders =
				new EnumMap<>(Instance.class);

		public FourWayInstanceProvider(final Instance priorityInstance) {
			super();
			mPriorityInstance = priorityInstance;
			for (final Instance instance : Instance.values()) {
				if (instance == mPriorityInstance) {
					mInstanceProviders.put(instance, new ConstructionCache<>(new DefaultTermVariableProvider()));
				} else {
					mInstanceProviders.put(instance, new ConstructionCache<>(new FreshTermVariableProvider(instance)));
				}
			}
		}

		private TermVariable getInstance(final IProgramVar pv, final EnumSet<Instance> allInstances) {
			if (allInstances.contains(mPriorityInstance)) {
				return mInstanceProviders.get(mPriorityInstance).getOrConstruct(pv);
			}
			return mInstanceProviders.get(allInstances.iterator().next()).getOrConstruct(pv);
		}
	}

	public boolean isWrittenOnReturn(final IProgramVar pv) {
		return mVarsAssignedOnReturn.contains(pv);
	}

	public boolean isModifiableByCallee(final IProgramNonOldVar pv) {
		return mModifiableGlobals.contains(pv);
	}

	public boolean inInParam(final ILocalProgramVar pv) {
		return mCalleeInParams.contains(pv);
	}

	public Set<TermVariable> getFreshTermVariables() {
		return mFreshTermVariables;
	}

}
