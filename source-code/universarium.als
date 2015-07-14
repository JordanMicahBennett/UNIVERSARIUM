--AUTHOR	: Jordan Micah Bennett
--NOTE : Please use magic layout in diagram view. This provides a more concise, vibrant view.
--VERSION : Alloy 4.2
--TITLE : Universarium, a model qua University


---OVERALL CORE HIERARCHY SUMMARY:
--[Major,Minor in Programme contains (Course contains (EntryRequirment contains Subject)] in Department in Faculty in University



--UNIT (Name=name, Alias=?)
--All things (mostly) are units.
--This is an appropriate way to handle inheritance and generics, such that Name/Alias occurs in all children.
--Thereafter, I take Alias to possess multiple exclusively occurring forms:
--i. Identifcation in Student
--ii. Identification in Staff
--iii. CourseCode in Course
--iv. CoursePrice in _Course
--v. Grade in Subject
--I take Name to symbolize name/title in:
--Student,StudentBalance,Staff,Building,Faculty,Department,Programme,Course,_Course,University,Subject
--NAME,ALIAS 
sig Name, Alias
{
}
abstract sig Unit 
{
	details : disj Name -> one Alias
}
--STUDENT (Name=name, Alias=identification)
sig Student extends Unit
{
	studentProgrammeDetails : Major -> ( Major + Minor ), --automatically allocates such that student has either Major and or Minor
	studentBalanceDetails : one StudentBalance
}
--STUDENTBALANCE (Name=name, Alias=ignore)
sig StudentBalance extends Unit
{
}
--STAFF (Name=name, Alias=identification)
abstract sig Staff extends Unit
{
}
--ACADEMIA,ADMINISTRATION,TECHNOLOGY,SUPPORT  (Name=name, Alias=identification)
sig Academia,Administration,Technology,Support extends Staff
{
}
--LECTURER,LIBRARIAN (Name=name, Alias=identification)
sig Lecturer extends Academia
{
	lecturerFacultyDetails : set Faculty
}
sig Librarian extends Academia
{
}
--ADMINISTRATIVEASSISTANT,SECRETARY (Name=name, Alias=identification)
sig AdministrativeAssistant extends Administration
{
}
sig Secretary extends Administration
{
}
--INFORMATIONOFFICER,ENGINEER (Name=name, Alias=identification)
sig InformationOfficer extends Technology
{
}
sig Engineer extends Technology
{
}
--OFFICEATTENDANT,CLEANER (Name=name, Alias=identification)
sig OfficeAttendant extends Support
{
}
sig Cleaner extends Support
{
}
--BUILDING (Name=name, Alias=identification)
sig Building in University
{
	buildingAdminstrationDetails : set AdministrativeAssistant -> ( AdministrativeAssistant + Secretary ), --building must have AdminstrativeAssistant and or Secretary
	buildingSupportDetails : set OfficeAttendant -> ( OfficeAttendant + Cleaner ),
	buildingTechnology : set InformationOfficer -> ( InformationOfficer + Engineer )
}
--REGISTRY,BURSARY,LIBRARY (Name=name, Alias=ignore)
one sig Registry in Building
{
	registryCourseDetails : set _Course
}
one sig Library in Building
{
	libraryLibrarianDetails : set Librarian
}
one sig Bursary in Building
{
}
--FACULTY (Name=name, Alias=ignore)
sig Faculty extends Unit
{
}
--DEPARTMENT (Name=name, Alias=ignore)
sig Department in Faculty
{
}
--PROGRAMME (Name=name, Alias=ignore)
sig Programme in Department
{
	programmeCourseDetails : set Course
}
--MAJOR,MINOR (Name=name, Alias=ignore)
sig Major, Minor in Programme
{
}
--COURSE (Name=name, Alias=identification)
sig Course extends Unit
{
	courseEntryRequirmentDetails : one EntryRequirement,
	courseLecturerDetails : one Lecturer
}
--_COURSE (Name=name, Alias=identification)
sig _Course extends Unit
{
}
--ENTRYREQUIREMENT (Name=name, Alias=identification)
sig EntryRequirement
{
	entryRequirementDetails : set Subject
}
--SUBJECT (Name=name, Alias=identification)
sig Subject extends Unit
{
}
--UNIVERSITY (Name=name, Alias=identification)
one sig University extends Unit
{
	students : set Student,
	staff : set Staff,
	faculties : set Faculty
}
--INVARIANT
fact invariant
{
	--enforce non-empty rule
	some students some staff some faculties some programmeCourseDetails

	--enforce no-sharing rule
	--i. no two students share id ( students may share programme/name, but not id )
	--ii. no two staff share id
	--iii. no two buildings share name (ignore alias-id)
	--iv. no two faculties share name (ignore alias-id)
	all u : Unit
	{
		no disj stu, stu' : u.students, sta, sta' : u.staff,  f, f' : u.faculties | stu.details -> Alias = stu'.details -> Alias and sta.details -> Alias = sta'.details -> Alias and f.details -> Name = f'.details -> Name
	}

	--enforce singularity rule
	all disj u : Unit, s : u.students | #u.details = 1 and #s.studentProgrammeDetails = 1
}
--BEHAVIOUR
pred display
{
}
run display for 6

pred register ( s : Student, c, c' : s.studentProgrammeDetails, b, b' : s.studentBalanceDetails, n' : Name, a' : Alias, a'' : Alias )
{
	--s symbolizes student
	--c symbolizes unadjusted student course set
	--c' symbolizes adjusted student course set after course addition
	--b symbolizes unadjusted student balance
	--b' symblizes adjusted student balance
	--n' symbolizes the name of the course being added
	--a' symbolizes the alias-course code of the course being added
	--a'' symbolizes the alias-price of the course being added
	c'.programmeCourseDetails = c.programmeCourseDetails + n' -> a' --adjust programme course set
	all r : Registry.registryCourseDetails | r.details -> Name = b.details -> Name => b'.details = b.details + n' -> a'' --adjust balance if added course name matches any course in registry
}
--FUNCTION
fun getProgrammeByLecturer ( l : Lecturer ):
	set Programme
	{
		--returns the intersection at lecturer faculties and universe of faculties, all of type Programme
		l.lecturerFacultyDetails & University.faculties
	}
