/* 
* PROMELA Model for Smart Health & Wellness Center
* Booking and Scheduling System Verification
* 
* Functional Requirements Modeled:
* FR6: Browse available time slots
* FR7: Book,reschedule,cancel appointents
* FR8: Send booking confirmations and alerts
* FR9: Staff update availability
* FR10: Staff view schedule
* FR11: User view booking history
* FR12: Prevent double - booking
*/ 
#define MAX_SLOTS 10
#define MAX_BOOKINGS 5
#define MAX_STAFF 3
#define MAX_USERS 3

/* Message types for communication*/ 
mtype = {
	BROWSE_REQUEST,BROWSE_RESPONSE,
	BOOK_REQUEST,BOOK_RESPONSE,BOOK_CONFIRM,
	RESCHEDULE_REQUEST,RESCHEDULE_RESPONSE,
	CANCEL_REQUEST,CANCEL_RESPONSE,CANCEL_CONFIRM,
	UPDATE_AVAILABILITY,AVAILABILITY_UPDATED,
	VIEW_SCHEDULE_REQUEST,SCHEDULE_RESPONSE,
	VIEW_HISTORY_REQUEST,HISTORY_RESPONSE,
	NOTIFICATION,REMINDER
};

/* Service types*/ 
mtype = { GYM, YOGA, CONSULTATION, PERSONAL_TRAINING};

/* Booking status*/ 
mtype = { AVAILABLE, BOOKED, CANCELLED };

/* Time slot structure*/ 
typedef TimeSlot {
	int slot_id; // Unique identifier for the time slot
	mtype service_type; // Type of service for the time slot
	int staff_id; // ID of the staff member assigned to this slot
	mtype status; // current status of the time slot (AVAILABLE, BOOKED, CANCELLED)
	int user_id; // who booked this slot (0 if not booked)
}

/* Booking record structure, this maintains the booking history and state*/ 
typedef Booking {
	int booking_id; // Unique identifier for the booking
	int slot_id; // ID of the time slot booked connected to TimeSlot
	int user_id; // ID of the user who made the booking
	int staff_id; // ID of the staff member assigned to this booking
	mtype service_type; // Type of service booked - gym, yoga etc
	mtype status; // current status of the booking - available, booked, cancelled
}

/* Staff availability structure*/ 
typedef StaffAvailability {
	int staff_id; // Unique identifier for the staff member
	bool available_slots[MAX_SLOTS]; // Array indicating availability for each time slot, initialized to true if false then not available
}

/* Global state variables*/ 
TimeSlot time_slots[MAX_SLOTS]; // total number of time slots available in the system
Booking bookings[MAX_BOOKINGS]; // total number of bookings made, initialized to 0
StaffAvailability staff_availability[MAX_STAFF]; // total number of staff members, initialized to true for all slots
int next_booking_id = 1; //booking id generator, starts from 1

/* Communication channels*/ 
chan user_to_system = [10] of { mtype,int,int,int }; // message type, user_id, booking_id, context dependant(slot_id, some int)
chan system_to_user = [10] of { mtype,int,int,int };
chan staff_to_system = [10] of { mtype,int,int,int };
chan system_to_staff = [10] of { mtype,int,int,int };
chan notification_channel = [10] of { mtype,int,int };

/* Initialize system with available time slots*/ 
init {
	int i;
	
	/* Initialize time slots*/ 
	for (i : 0 .. MAX_SLOTS - 1) {
		time_slots[i].slot_id = i;
		time_slots[i].service_type = GYM;/* Default service*/ 
		time_slots[i].staff_id = -1; /* No staff assigned initially*/
		time_slots[i].status = AVAILABLE;
		time_slots[i].user_id = -1; /* No user booked initially*/
	}
	
	/* Initialize staff availability*/ 
	for (i : 0 .. MAX_STAFF - 1){
		staff_availability[i].staff_id = i;
		int j;
		for (j: 0 .. MAX_SLOTS - 1) {
			staff_availability[i].available_slots[j] = true;
		}
	}
	
	/* Start system processes*/ 
	run BookingSystem();
	run NotificationSystem();
	run User(1);
	run User(2);
	run Staff(1);
	run Staff (2);
}

/* FR6: Browse available time slots*/ 
inline browse_available_slots(user_id, service_type) {
	int i;
	int available_count = 0;
	
	for (i : 0 .. MAX_SLOTS - 1) {
		if  :: (time_slots[i].status == AVAILABLE && 
			staff_availability[time_slots[i].staff_id].available_slots[i]) -> 
			available_count++
		:: else -> skip
		fi
	}
	
	system_to_user ! BROWSE_RESPONSE,user_id,available_count,0;
}

/* FR12: Check for double - booking prevention*/ 
inline check_double_booking(slot_id,staff_id) {
	/* Check if slot is already booked*/ 
	assert(time_slots[slot_id].status == AVAILABLE);
	/* Check if staff is available for this slot*/ 
	assert(staff_availability[staff_id].available_slots[slot_id] == true);
}

/* FR7: Book appointment*/ 
inline book_appointment (user_id, slot_id, service_type) {
	
    int staff_id = time_slots[slot_id].staff_id;
	
	/* FR12: Prevent double - booking*/ 
	if  :: (time_slots[slot_id].status == AVAILABLE && 
		staff_availability[staff_id].available_slots[slot_id]) -> 
		check_double_booking(slot_id,staff_id);
		
		/* Update time slot*/ 
		time_slots[slot_id].status = BOOKED;
		time_slots[slot_id].user_id = user_id;
		
		/* Create booking record*/ 
		bookings[next_booking_id - 1].booking_id = next_booking_id;
		bookings[next_booking_id - 1].slot_id = slot_id;
		bookings[next_booking_id - 1].user_id = user_id;
		bookings[next_booking_id - 1].staff_id = staff_id;
		bookings[next_booking_id - 1].service_type = GYM;
		bookings[next_booking_id - 1].status = BOOKED;
		
		next_booking_id++;
		
		/* FR8: Send booking confirmation*/ 
		notification_channel!BOOK_CONFIRM,user_id,slot_id;
		system_to_user!BOOK_RESPONSE,user_id,1,slot_id;/* Success*/ 
	:: else -> 
		system_to_user!BOOK_RESPONSE,user_id,0,slot_id;/* Failure*/ 
	fi
}

/* FR7: Cancel appointment*/ 
inline cancel_appointment(user_id,booking_id) {
	int i;
	bool found = false;
	
	for (i : 0 .. MAX_BOOKINGS - 1) {
		if  :: (bookings[i].booking_id == booking_id && 
			bookings[i].user_id == user_id && 
			bookings[i].status == BOOKED) -> 
			
			/* Update booking status*/ 
			bookings[i].status = CANCELLED;
			
			/* Free up time slot*/ 
			time_slots[bookings[i].slot_id].status = AVAILABLE;
			time_slots[bookings[i].slot_id].user_id = 0;
			
			found = true;
			
			/* FR8: Send cancellation confirmation*/ 
			notification_channel!CANCEL_CONFIRM,user_id,booking_id;
			
			break
		:: else -> skip
		fi
	}
	
	if  :: found -> system_to_user!CANCEL_RESPONSE,user_id,1,booking_id;/* Success*/ 
	:: else -> system_to_user!CANCEL_RESPONSE,user_id,0,booking_id;/* Failure*/ 
	fi
}

/* FR7: Reschedule appointment*/ 
inline reschedule_appointment(user_id,old_booking_id,new_slot_id) {
	int i;
	bool found = false;
	
	for (i : 0 .. MAX_BOOKINGS - 1) {
		if :: (bookings[i].booking_id == old_booking_id && 
			bookings[i].user_id == user_id && 
			bookings[i].status == BOOKED) -> 
			
			/* Check if new slot is available*/ 
			if :: (time_slots[new_slot_id].status == AVAILABLE) -> 
				
				/* Cancel old booking*/ 
				time_slots[bookings[i].slot_id].status = AVAILABLE;
				time_slots[bookings[i].slot_id].user_id = 0;
				
				/* Book new slot*/ 
				time_slots[new_slot_id].status = BOOKED;
				time_slots[new_slot_id].user_id = user_id;
				
				/* Update booking record*/ 
				bookings[i].slot_id = new_slot_id;
				found = true;
				break
				
			:: else -> skip/* New slot not available*/ 
			fi
		:: else -> skip
		fi
	}
	
	if  :: found -> system_to_user!RESCHEDULE_RESPONSE,user_id,1,new_slot_id;
	:: else -> system_to_user!RESCHEDULE_RESPONSE,user_id,0,new_slot_id;
	fi
}

/* FR11: View booking history*/ 
inline view_booking_history(user_id) {
	int i;
	int user_bookings = 0;
	
	for (i: 0 .. MAX_BOOKINGS - 1) {
		if  :: (bookings[i].user_id == user_id && bookings[i].booking_id > 0) -> 
			user_bookings++
		:: else -> skip
		fi
	}
	system_to_user!HISTORY_RESPONSE,user_id,user_bookings,0;
}

/* FR9: Staff update availability*/ 
inline update_staff_availability(staff_id,slot_id,available) {
	staff_availability[staff_id].available_slots[slot_id] = available;
	system_to_staff!AVAILABILITY_UPDATED,staff_id,slot_id,available;
}

/* FR10: Staff view schedule*/ 
inline view_staff_schedule(staff_id) {
	int i;
	int appointments = 0;
	
	for (i: 0 .. MAX_SLOTS - 1) {
		if  :: (time_slots[i].staff_id == staff_id && time_slots[i].status == BOOKED) -> 
			appointments++
		:: else -> skip
		fi
	}
	
	system_to_staff!SCHEDULE_RESPONSE,staff_id,appointments,0;
}

/* Main Booking System Process*/ 
proctype BookingSystem() {
	mtype msg_type;
	int param1,param2,param3;
	
	do
	:: user_to_system ? msg_type, param1, param2, param3 ->  // received a message from user? if yes get the message type and parameters and start the loop, untill that its blocked
		if  :: msg_type == BROWSE_REQUEST -> 
			    browse_available_slots (param1,param2);
			
		    :: msg_type == BOOK_REQUEST -> 
			    book_appointment(param1,param2,param3);
			
		    :: msg_type == CANCEL_REQUEST -> 
			    cancel_appointment(param1,param2);
			
		    :: msg_type == RESCHEDULE_REQUEST -> 
			    reschedule_appointment(param1,param2,param3);
			
		    :: msg_type == VIEW_HISTORY_REQUEST -> 
			    view_booking_history(param1);
		fi
		
	:: staff_to_system?msg_type,param1,param2,param3 -> 
		if  :: msg_type == UPDATE_AVAILABILITY -> 
			update_staff_availability(param1,param2,param3);
			
		:: msg_type == VIEW_SCHEDULE_REQUEST -> 
			view_staff_schedule(param1);
		fi
	od
}

/* FR8: Notification System*/ 
proctype NotificationSystem() {
	mtype msg_type;
	int user_id,param;
	
	do
	:: notification_channel ? msg_type, user_id, param -> 
		/* Send notifications to users*/ 
		system_to_user ! NOTIFICATION, user_id, 0, param;
	od
}

/* User Process*/ 
proctype User(int user_id) {
	mtype msg_type;
	int param1,param2,response;
	
	do
	:: /* FR6: Browse available slots*/ 
		user_to_system ! BROWSE_REQUEST, user_id, 0, 0;
		system_to_user ? msg_type, param1, param2, response;
		assert(msg_type == BROWSE_RESPONSE);
		
	:: /* FR7: Book appointment*/ 
		user_to_system!BOOK_REQUEST,user_id,1,0;/* Book slot 1*/ 
		system_to_user?msg_type,param1,param2,response;
		assert(msg_type == BOOK_RESPONSE);
		
	:: /* FR7: Cancel appointment*/ 
		user_to_system!CANCEL_REQUEST,user_id,1,0;/* Cancel booking 1*/ 
		system_to_user?msg_type,param1,param2,response;
		assert(msg_type == CANCEL_RESPONSE);
		
	:: /* FR11: View booking history*/ 
		user_to_system!VIEW_HISTORY_REQUEST,user_id,0,0;
		system_to_user?msg_type,param1,param2,response;
		assert(msg_type == HISTORY_RESPONSE);
		
	:: /* Receive notifications*/ 
		system_to_user?msg_type,param1,param2,response;
		/* Process notification*/ 
		
	:: break
	od
}

/* Staff Process*/ 
proctype Staff(int staff_id) {
	mtype msg_type;
	int param1,param2,response;
	
	do
	:: /* FR9: Update availability*/ 
		staff_to_system!UPDATE_AVAILABILITY,staff_id,1,1;/* Set slot 1 available*/ 
		system_to_staff?msg_type,param1,param2,response;
		assert(msg_type == AVAILABILITY_UPDATED);
		
	:: /* FR10: View schedule*/ 
		staff_to_system!VIEW_SCHEDULE_REQUEST,staff_id,0,0;
		system_to_staff?msg_type,param1,param2,response;
		assert(msg_type == SCHEDULE_RESPONSE);
	:: break 
	od
}