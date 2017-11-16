/*
DD 2017-11-16

The Plugin de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator has thrown an exception:
java.lang.ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler.visit(CHandler.java:1156)
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher.dispatch(PRDispatcher.java:352)
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler.visit(CHandler.java:2477)
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PRDispatcher.dispatch(PRDispatcher.java:322)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CTranslationOnly.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/loop-industry-pattern/ofuf_4_true-unreach-call.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult" 

*/

void main()
{
	return  "" , 0;
}
