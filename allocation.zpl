#
# Speciality tuple: <id_speciality,speciality_name,periodUnits_need,suspencion_rate>
#
set RAWSpecialities := { read "specialities.csv" as "<1n,2s,3n,4n>" skip 1 };

#
# Doctor tuple: <id_doctor,id_speciality,t_max_day,t_max_week>
#
set RAWDoctors := { read "doctors.csv" as "<1n,3n,5n,6n>" skip 1 };

#
# Surgery tuple: <id_surgery,id_speciality,priority>
#
set RAWSurgeries := { read "surgeries.csv" as "<1n,3n,5n>" skip 1 };

set Rooms := {1..8};
set Days := {1..5};
param MAX_TIME_UNIT := 24;
set PeriodUnits := { 1 .. MAX_TIME_UNIT };

set PeriodIndexes := { <speciality,size,periodUnit> in proj(RAWSpecialities, <1,3>)*PeriodUnits with (periodUnit + size) <= MAX_TIME_UNIT };
set SizedPeriods[<size,timeUnit> in proj(PeriodIndexes, <2,3>)] := { timeUnit to (timeUnit + (size - 1)) by 1 };

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

var x[Allocations] binary;

maximize allocations: sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations : x[surgery,speciality,doctor,room,day,size,periodUnit];

#
# Every surgery with priority 1 have to be done by a doctor in a given room, day and a time block.
#
subto const_1: forall <critical_surgery> in CriticalSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with critical_surgery == surgery : x[surgery,speciality,doctor,room,day,size,periodUnit] == 1;

#
# The others regular surgeries should be done by a doctor in a given room, day and a time block.
#
subto const_2: forall <major_surgery> in MajorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with major_surgery == surgery : x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Minor surgeries with suspencion rate below 50% can be allocated.
#
subto const_3: forall <minor_surgery,suspencion_rate> in MinorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with minor_surgery == surgery and suspencion_rate < 0.5 : x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Minor surgeries with suspencion rate above 50% cannot be allocated.
#
subto const_4: forall <minor_surgery,suspencion_rate> in MinorSurgeries do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with minor_surgery == surgery and suspencion_rate >= 0.5 : x[surgery,speciality,doctor,room,day,size,periodUnit] == 0;

#
# A room in a given a day and time period can be only allocated once.
#
subto const_5: forall <obs_room,obs_day,obs_size,obs_periodUnit> in Rooms*Days*proj(PeriodIndexes, <2,3>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_room == room and obs_day == day and
		card(SizedPeriods[obs_size,obs_periodUnit] inter SizedPeriods[size,periodUnit]) > 0 :
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# A doctor in a given day and time period can be only allocated once.
#
subto const_7: forall <obs_doctor,obs_room,obs_day,obs_size,obs_periodUnit> in proj(Allocations, <3,4,5,6,7>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with obs_doctor == obs_doctor and obs_room == room and obs_day == day and 
		card(SizedPeriods[obs_size,obs_periodUnit] inter SizedPeriods[size,periodUnit]) > 0 : 
			x[surgery,speciality,doctor,room,day,size,periodUnit] <= 1;

#
# Doctor's max daily time
#
subto const_8: forall <observed_day,observed_doctor,t_max_day> in Days*proj(RAWDoctors, <1,3>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with observed_doctor == doctor and observed_day == day: 
			x[surgery,speciality,doctor,room,day,size,periodUnit]*card(SizedPeriods[size,periodUnit]) <= t_max_day;

#
# Doctor's max weekly time
#
subto const_9: forall <observed_doctor,t_max_week> in proj(RAWDoctors, <1,4>) do
	sum <surgery,speciality,doctor,room,day,size,periodUnit> in Allocations
		with observed_doctor == doctor : 
			x[surgery,speciality,doctor,room,day,size,periodUnit]*card(SizedPeriods[size,periodUnit]) <= t_max_week;
