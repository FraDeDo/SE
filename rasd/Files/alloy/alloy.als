// A Farmer can be associated to multiple Production Fields -----
// A Production Field has one and only one crop -----
// Only farmers participate to forum; at least one farmer per forum ------
// Only one user with a determined username exists ---------
// One Account for one user ----------
// Agronomist and TPM must be associated to one and only one license, and viceversa -------
// All Password with at least one Account -------
// Agronomist to one Area, an Area involves multiple location; One Farmer one Location, and viceversa -----
// Location are relative to only one Area; two locations have different areas --------
// All areas are covered by at least one agronomist	 --------
// All production fields have one and only one owner/farmer	--------
// Technical Fact: Dates D1 and D2 are equal iff they share the same parameters



//------Authentication Part-------//

sig Email{}

sig Password{}

sig Account{
	mail: one Email,		
	pass: one Password
}

abstract sig User{
	registration: one Account  
}

//------Farmer Production And Area Part------//

sig Location{}

sig Area{
	locs: some Location
}

abstract sig Suggestion{}

sig FarmerSuggestion extends Suggestion{}

sig DirectSuggestion extends Suggestion {
	direct: one Farmer
}

sig Crop{
	suggestions: set Suggestion
}

sig Number{}
sig Day{}
sig Month{}
sig Year{}
sig Date{
	day: one Day,				
	month: one Month,
	year: one Year
}
sig Fertilizer{}
sig Iot{}
sig Feedback{} 

sig ProductionField{
	crop: one Crop,
	amount: one Number,
	date: one Date,
	fert: lone Fertilizer,
	iot: set Iot,
	updates: set Feedback
}

sig HarvestedField extends ProductionField{   			  
	harvested: one Number,
	finalDate: one Date
}

sig Farmer extends User{
	location: one Location,	
	fields: set ProductionField,
	messageRequest: set Request,
	messageResponseF: set Request,
	author: set Topic,
	comment: set Topic,
	suggest: set FarmerSuggestion
}

sig Agronomist extends User{
	areaofInterest: one Area,
	legalAgronomistLicense: one AgronomistLicense,
	dailyPlans: some DailyPlan,
	messageResponseA: set Request,
	agrosuggest: set DirectSuggestion
}

sig TPM extends User{
	legalTPMLicense: one TPMLicense
}

//------Daily Plan------//

sig DailyPlan{
	dateDailyPlan: one Date,
	visitedFarmers: set Farmer		
}

//------Licenses Part-------//

abstract sig License{}

sig AgronomistLicense extends License{}

sig TPMLicense extends License{}

//----Request----/

sig Request{}

//------Forum------//

sig Topic {
	forum: one Forum	
}

one sig Forum{}

//------Facts------//

fact DifferentDateInHarvestField{
	all h:HarvestedField | h.finalDate != h.date
}

fact OneDirectSuggestionFromOneAgro {			//All directs suggestions are written by only one agronomist
	all d:DirectSuggestion | one a:Agronomist | d in a.agrosuggest
}

fact OneSuggestionOneFarmer{					//All farmer suggestions are written by only one Farmer
	all s:FarmerSuggestion | one f:Farmer | s in f.suggest
}

fact UpdatesOneProductionField{					//All updates are related to one production field
	all f:Feedback| one p:ProductionField | f in p.updates 
}

fact AllSuggestionsOneCrop{					//All suggestions are related to one crop
	all s:Suggestion | one c:Crop | s in c.suggestions
}

fact AllFertilizerAssociated {
	all f:Fertilizer, p:ProductionField | f in p.fert
}

fact DifferentDatesDifferentTimestamp {   				//There exists oly different dates
	all da1, da2:Date | da1.day=da2.day and da1.month=da2.month and da1.year=da2.year implies da1=da2
}

fact AccountOneMail {
	all e:Email | #(mail.e)=1   // There can't be two or more accounts with the same email,  and all emails are associated to
						  // an account
}

fact AccountOneUser {
	all a:Account | #(registration.a)=1   // All User have one and only one account and there can't be two users with the same account
								   
}

fact AllPassWithAtLeastOneAccount { 
	all p: Password | some a: Account | p in a. pass // All Password must be associated with at least one Account
}


fact TPMOneLicense {
	all l:TPMLicense | #(legalTPMLicense.l)=1   // One and only one license for TPM.
								   	      // Every license has a different owner.
}

fact AgronomistOneLicense {
	all l:AgronomistLicense | #(legalAgronomistLicense.l)=1   // One and only one license for Agronomist.
								 				      // Every license has a different owner.
}

fact LocationOneArea {
	all l:Location | #(locs.l)=1   // Two different locations are relative to different Areas						 
}

fact LocationOneFarmer {
	all l:Location | #(location.l)=1   // Two different locations are relative to different Farmers					 
}

fact AllAreasCoveredByAtLeastOneAgronomist {
	all a:Area | #(areaofInterest.a)>=1   // All areas are covered by at least one agronomist			 
}

fact FieldsForDifferentFarmers{
	all p:ProductionField | #(fields.p)=1   // All production fields have one and only one owner/farmer	 
}

fact IotForProductionFields{
	all i:Iot | one p:ProductionField | i in p.iot
}

fact CropInProductionFields{
	all c:Crop | some p:ProductionField | c in p.crop
}

fact DailyPlansdifferentdates{
	all d1,d2:DailyPlan | (d1.dateDailyPlan = d2.dateDailyPlan) implies d1 = d2 
}

fact DailyPlanToOneAgronomist{						//All Daily Plan to Exactly One Agronomist
	all d:DailyPlan | one a:Agronomist | d in a.dailyPlans 
}

//----At Least Twice a Year-----///

fun DateAndYearInWhichFarmerHasBeenVisited[f: Farmer]: set year {
	 ((visitedFarmers.f).dateDailyPlan) <: year
}

pred VisitedTwiceAYear[f:Farmer]  {
	all y:Year | #(DateAndYearInWhichFarmerHasBeenVisited[f].y)>=2 
}

//----Forum----//

fact OneTopicOneAuthor{
	all t:Topic | one f:Farmer | t in f.author
}

fact NotOnlyAuthorComment{
	all t:Topic, f:Farmer | (t in f.author) and (t in f.comment) implies #(comment.t) >= 1
}

//----Request----//

fact OneRequestResponsebyFarmerorAgronomist{       //The response can't received by both a farmer and an agronomist
	no r:Request |  one a:Agronomist, f:Farmer | (r in f.messageResponseF) and (r in a.messageResponseA) 
}

fact OneRequestOneMessageRequest{
	all r:Request | one f:Farmer | r in f.messageRequest
}

fact NoBothRequestandResponse{      //A farmer can't response to the request he did
	no f:Farmer, r:Request | r in f.messageRequest and r in f.messageResponseF
}

fact OneResponeF{
	all r:Request | #(messageResponseF.r) < 2
}

fact OneResponseA{
	all r:Request | #(messageResponseA.r) < 2
}


pred World1{
	#Farmer =2 and
	#Agronomist = 1 and
	#HarvestedField = 0 and
	#Topic = 0 and
	#Suggestion = 0 and
	#Request = 0 and
	#DailyPlan = 3
}


pred World2{
	#Farmer =2 and
	#Agronomist = 2 and
	#ProductionField = 2 and
	#HarvestedField = 1
	#updates = 3
	#DirectSuggestion = 1 and 
	#Topic = 0 and
	#Request = 0 and
	#DailyPlan = 2 and
	#Number = 3
}


pred World3{
	#Farmer =2 and
	#Agronomist = 1 and
	#ProductionField = 0 and
	#HarvestedField = 0 and  
	#Topic = 2 and
	#Request = 4 and
	#messageResponseA = 2
}



pred World4{
	#Farmer =2 and
	#Agronomist = 1 and
	#ProductionField = 3 and
	#DirectSuggestion = 2 and
	#FarmerSuggestion = 2 and
	#Crop = 3  and
	#Topic = 0 and
	#Request = 0 
}


run show for 4



