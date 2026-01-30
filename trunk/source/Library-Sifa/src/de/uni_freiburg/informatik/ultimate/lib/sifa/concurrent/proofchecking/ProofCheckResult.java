package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Result of a proof check operation.
 */
public class ProofCheckResult {

	private final boolean mIsValid;
	private final List<String> mViolations;

	private ProofCheckResult(final boolean isValid, final List<String> violations) {
		mIsValid = isValid;
		mViolations = new ArrayList<>(violations);
	}

	public static ProofCheckResult valid() {
		return new ProofCheckResult(true, Collections.emptyList());
	}

	public static ProofCheckResult invalid(final List<String> violations) {
		return new ProofCheckResult(false, violations);
	}

	public static ProofCheckResult invalid(final String violation) {
		return new ProofCheckResult(false, List.of(violation));
	}

	public boolean isValid() {
		return mIsValid;
	}

	public List<String> getViolations() {
		return Collections.unmodifiableList(mViolations);
	}
}
