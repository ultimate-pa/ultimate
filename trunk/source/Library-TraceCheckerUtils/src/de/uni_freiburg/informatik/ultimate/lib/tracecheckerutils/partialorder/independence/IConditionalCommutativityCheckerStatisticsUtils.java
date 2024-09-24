package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

// TODO what is the purpose of this interface?
public interface IConditionalCommutativityCheckerStatisticsUtils {
	public void startStopwatch();

	public void stopStopwatch();

	public void addDFSRestart();

	public void addIAIntegration();

	public void addConditionCalculation();

	public void addTraceCheck();

	public void addImperfectProof();
}
