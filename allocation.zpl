#
# Speciality tuple: <id_speciality,speciality_name,periodUnits_need,suspencion_rate>
#
set RAWSpecialities := { read "specialities.csv" as "<1n,2s,3n,4n>" skip 1 };

#
# Doctor tuple: <id_doctor,id_speciality,tmax_day,tmax_week>
#
set RAWDoctors := { read "doctors.csv" as "<1n,3n,5n,6n>" skip 1 };

#
# Surgery tuple: <id_surgery,id_speciality,priority>
#
set RAWSurgeries := { read "surgeries.csv" as "<1n,3n,5n>" skip 1 };

set Rooms := {1..8};
set Days := {1..5};
param MAX_TIME_UNIT := 16;
set PeriodUnits := { 1 .. MAX_TIME_UNIT };

set PeriodIndexes := { <speciality,size,periodUnit> in proj(RAWSpecialities, <1,3>)*PeriodUnits with (periodUnit + size) <= MAX_TIME_UNIT };
set SizedPeriods[<size,timeUnit> in proj(PeriodIndexes, <2,3>)] := { timeUnit to (timeUnit + (size - 1)) by 1 };

param ShadowedPeriods[ <size_1,periodUnit_1,size_2,periodUnit_2> in proj(PeriodIndexes, <2,3>)*proj(PeriodIndexes, <2,3>) ] := 
	if ( card(SizedPeriods[size_1,periodUnit_1] inter SizedPeriods[size_2,periodUnit_2]) > 0)
		then 1
	else 0
	end;

set CriticalSurgeries := proj({ <id_surgery,id_speciality,prior> in RAWSurgeries with prior == 1 }, <1>);
set MajorSurgeries := proj({ <id_surgery,id_speciality,prior> in RAWSurgeries with prior == 2 }, <1>);
set MinorSurgeries := proj({ <id_surgery,id_speciality,prior,obs_speciality,suspencion_rate> in RAWSurgeries*proj(RAWSpecialities, <1,4>)
	with id_speciality == obs_speciality and prior == 3 }, <1,5>);

set AllSurgeries := CriticalSurgeries + MajorSurgeries + proj(MinorSurgeries, <1>);

#
# Index sets
#
set Doctors := proj(RAWDoctors, <1>);

param DoctorsAvaiability[Doctors*PeriodUnits*Days] := |1, 2, 3, 4, 5|
						|1,1|1, 1, 1, 1, 1| default 1;

#
# Main set
#
set Allocations := proj( {<surgery,s1,doctor,s2,room,day,s3,size,periodUnit> in proj(RAWSurgeries, <1,2>)*proj(RAWDoctors, <1,2>)*Rooms*Days*PeriodIndexes
	with s1 == s2 and s1 == s3 and DoctorsAvaiability[doctor,periodUnit,day] == 1}, <1,2,3,5,6,8,9> );


#
# Details
#
do print "";
do print "Specialities: ", card(RAWSpecialities);
do print "Surgeries: ", card(RAWSurgeries);
do print "Doctors: ", card(RAWDoctors);

do print "";
do print "Time units/day: ", MAX_TIME_UNIT;
do print "Period indexes: ", card(PeriodIndexes);
do print "Doctor's max availiable attendance time: ", sum <d,t> in proj(RAWDoctors, <1,4>) : t;

set DemandedTime := proj({<spec,tUnits,s_rate,surg,spec_s,prior> in proj(RAWSpecialities, <1,3,4>)*RAWSurgeries with spec == spec_s}, <1,2,3,4,6>);
do print "Total demanded time: ", sum <t,s> in proj(DemandedTime, <2,4>) : t;
do print "Total demanded time: ", sum <t,s> in 
	proj({<spec,tUnits,s_rate,surg,prior> in DemandedTime with s_rate < 0.5 or prior < 3}, <2,4>) : t, " (applying suspencion rate criteria)";

do print "";
do print "Variables: ", card(Allocations);
do print "";

var x[Allocations] binary;

do print "obj function";
maximize allocations: sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations :
	x[surgery,speciality,doctor,room,day,size,periodUnit];

#
# Every surgery with priority 1 have to be done by a doctor in a given room, day and a time block.
#
do print "const_1";
subto const_1: forall <critical_surgery> in CriticalSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with critical_surgery == surgery :
			x[surgery,speciality,doctor,room,day,size,periodUnit] == 1;

#
# The others regular surgeries should be done by a doctor in a given room, day and a time block.
#
do print "const_2";
subto const_2: forall <major_surgery> in MajorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with major_surgery == surgery :
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Minor surgeries with suspencion rate below 50% can be allocated.
#
do print "const_3";
subto const_3: forall <minor_surgery,suspencion_rate> in MinorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with minor_surgery == surgery and suspencion_rate < 0.5 :
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Minor surgeries with suspencion rate above 50% cannot be allocated.
#
do print "const_4";
subto const_4: forall <minor_surgery,suspencion_rate> in MinorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with minor_surgery == surgery and suspencion_rate >= 0.5 :
			x[surgery,speciality,doctor,room,day,size,periodUnit] == 0;

#
# A room in a given a day and time period can be only allocated once.
#
do print "const_5_1";
subto const_5_1: forall <obs_room,obs_day,obs_size,obs_periodUnit> in proj(Allocations, <4,5,6,7>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_room == room and obs_day == day and ShadowedPeriods[obs_size,obs_periodUnit,size,periodUnit] == 1 :
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# A room can be only scheduled MAX_TIME_UNIT per day.
#
do print "const_5_2";
subto const_5_2: forall <obs_room,obs_day> in proj(Allocations, <4,5>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_room == room and obs_day == day :
			x[surgery,speciality,doctor,room,day,size,periodUnit]*size <= MAX_TIME_UNIT;

#
# A doctor in a given day and time period can be only allocated once.
#
do print "const_6";
subto const_6: forall <obs_doctor,obs_day,obs_size,obs_periodUnit> in proj(Allocations, <3,5,6,7>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_doctor == doctor and obs_day == day and ShadowedPeriods[obs_size,obs_periodUnit,size,periodUnit] == 1 : 
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Doctor's max daily time
#
set C7 := proj({<doctor,tmax_day,obs_doctor,day> 
	in proj(RAWDoctors, <1,3>)*proj(Allocations, <3,5>) with doctor == obs_doctor}, <1,2,4>);

do print "const_7";
subto const_7: forall <obs_doctor,tmax_day,obs_day> in C7 do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_doctor == doctor and obs_day == day : 
			x[surgery,speciality,doctor,room,day,size,periodUnit]*size <= tmax_day;

#
# Doctor's max weekly time
#
#do print "const_8";
#subto const_8: forall <obs_doctor,tmax_week> in proj(RAWDoctors, <1,4>) do
#	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
#		with obs_doctor == doctor :
#			x[surgery,speciality,doctor,room,day,size,periodUnit]*size <= tmax_week;
