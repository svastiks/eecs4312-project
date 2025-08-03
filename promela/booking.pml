/* 
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
	BOOK_REQUEST, BOOK_RESPONSE,
	CANCEL_REQUEST, CANCEL_RESPONSE,
	RESCHEDULE_REQUEST, RESCHEDULE_RESPONSE,
	UPDATE_AVAILABILITY, AVAILABILITY_UPDATED
};

/* Service types*/ 
mtype = { GYM, YOGA, CONSULTATION, PERSONAL_TRAINING};

/* Booking status*/ 
mtype = { AVAILABLE, BOOKED, CANCELLED };

/* Time slot structure*/ 
typedef TimeSlot {
	byte slot_id; // Unique identifier for the time slot
	byte service_type; // Type of service for the time slot
	byte staff_id; // ID of the staff member assigned to this slot
	byte status; // current status of the time slot (AVAILABLE, BOOKED, CANCELLED)
	byte user_id; // who booked this slot (0 if not booked)
}

/* Booking record structure, this maintains the booking history and state*/ 
typedef Booking {
	byte booking_id; // Unique identifier for the booking
	byte slot_id; // ID of the time slot booked connected to TimeSlot
	byte user_id; // ID of the user who made the booking
	byte staff_id; // ID of the staff member assigned to this booking
	byte service_type; // Type of service booked - gym, yoga etc
	byte status; // current status of the booking - available, booked, cancelled
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
int next_booking_id = 0; //booking id generator, starts from 0

/* Communication channels*/ 
chan user_to_system = [10] of { mtype,int,int,int }; // message type, user_id, slot_id, booking_id
chan system_to_user = [10] of { mtype,int,int,int };
chan staff_to_system = [10] of { mtype,int,int,int };
chan system_to_staff = [10] of { mtype,int,int,int };

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
	run User(1);
	run User(2);
	run Staff(1);
	run Staff(2);
}

/* FR6: Browse available time slots*/ 
inline browse_available_slots(service_type, user_id) {
	int i;
	int available_count = 0;
	
	for (i : 0 .. MAX_SLOTS - 1) {
		if  :: (time_slots[i].status == AVAILABLE && 
			staff_availability[time_slots[i].staff_id].available_slots[i]) -> 
			available_count++
		:: else -> skip
		fi
	}
	
	system_to_user ! BROWSE_RESPONSE, user_id, available_count, 0;
}

/* FR12: Check for double - booking prevention*/ 
inline check_double_booking(slot_id,staff_id) {
	/* Check if slot is already booked*/ 
	assert(time_slots[slot_id].status == AVAILABLE);
	/* Check if staff is available for this slot*/ 
	assert(staff_availability[staff_id].available_slots[slot_id] == true);
}

/* FR7: Book appointment*/ 
inline book_appointment(msg_type, param1, param2) {
    int staff_id;
    
    /* Assign a staff member if none assigned */
    if
    :: (time_slots[param2].staff_id == -1) -> staff_id = 0;
    :: else -> staff_id = time_slots[param2].staff_id;
    fi;
	
	/* FR12: Prevent double - booking*/ 
	if
	:: (time_slots[param2].status == AVAILABLE && 
		staff_id >= 0 && staff_id < MAX_STAFF &&
		staff_availability[staff_id].available_slots[param2]) -> 
		check_double_booking(param2, staff_id);
		
		/* Update time slot*/ 
		time_slots[param2].status = BOOKED;
		time_slots[param2].user_id = param1;
		time_slots[param2].service_type = msg_type;
		
		/* If no staff assigned, assign one */
		if
		:: (time_slots[param2].staff_id == -1) -> time_slots[param2].staff_id = 0
		:: else -> skip
		fi;
		
		/* Create booking record*/ 
		bookings[next_booking_id].booking_id = next_booking_id + 1;
		bookings[next_booking_id].slot_id = param2;
		bookings[next_booking_id].user_id = param1;
		bookings[next_booking_id].staff_id = staff_id;
		bookings[next_booking_id].service_type = msg_type;
		bookings[next_booking_id].status = BOOKED;
		
		next_booking_id++;
		
		system_to_user!BOOK_RESPONSE,param1,1,param2;/* Success */ 
	:: else -> 
		system_to_user!BOOK_RESPONSE,param1,0,param2;/* Failure */ 
	fi
}

/* FR7: Cancel appointment*/ 
inline cancel_appointment(param1, param2) {
	int i;
	bool found = false;
	
	for (i : 0 .. MAX_BOOKINGS - 1) {
		if  :: (bookings[i].booking_id == param2 && 
			bookings[i].user_id == param1 && 
			bookings[i].status == BOOKED) -> 
			
			/* Update booking status*/ 
			bookings[i].status = CANCELLED;
			
			/* Free up time slot*/ 
			time_slots[bookings[i].slot_id].status = AVAILABLE;
			time_slots[bookings[i].slot_id].user_id = -1;
			
			found = true;
			break
		:: else -> skip
		fi
	}
	
	if  :: found -> system_to_user!CANCEL_RESPONSE,param1,1,param2;/* Success*/ 
	:: else -> system_to_user!CANCEL_RESPONSE,param1,0,param2;/* Failure*/ 
	fi
}

/* FR7: Reschedule appointment*/ 
inline reschedule_appointment(param1, param2, param3) {
	int i;
	bool found = false;
	
	for (i : 0 .. MAX_BOOKINGS - 1) {
		if :: (bookings[i].booking_id == param2 && 
			bookings[i].user_id == param1 && 
			bookings[i].status == BOOKED) -> 
			
			/* Check if new slot is available*/ 
			if :: (time_slots[param3].status == AVAILABLE) -> 
				
				/* Cancel old booking*/ 
				time_slots[bookings[i].slot_id].status = AVAILABLE;
				time_slots[bookings[i].slot_id].user_id = -1;
				
				/* Book new slot*/ 
				time_slots[param3].status = BOOKED;
				time_slots[param3].user_id = param1;
				
				/* Update booking record*/ 
				bookings[i].slot_id = param3;
				found = true;
				break
				
			:: else -> skip/* New slot not available*/ 
			fi
		:: else -> skip
		fi
	}
	
	if  :: found -> system_to_user!RESCHEDULE_RESPONSE,param1,1,param3;
	:: else -> system_to_user!RESCHEDULE_RESPONSE,param1,0,param3;
	fi
}

/* FR11: View booking history*/ 
inline view_booking_history(param1) {
	int i;
	int user_bookings = 0;
	
	for (i: 0 .. MAX_BOOKINGS - 1) {
		if  :: (bookings[i].user_id == param1 && bookings[i].booking_id > 0) -> 
			user_bookings++
		:: else -> skip
		fi
	}
	system_to_user!HISTORY_RESPONSE,param1,user_bookings,0;
}

/* FR9: Staff update availability*/ 
inline update_staff_availability(param1,param2,param3) {
	staff_availability[param1].available_slots[param2] = param3;
	system_to_staff!AVAILABILITY_UPDATED,param1,param2,param3;
}

/* FR10: Staff view schedule*/ 
inline view_staff_schedule(param1) {
	int i;
	int appointments = 0;
	
	for (i: 0 .. MAX_SLOTS - 1) {
		if  :: (time_slots[i].staff_id == param1 && time_slots[i].status == BOOKED) -> 
			appointments++
		:: else -> skip
		fi
	}
	
	system_to_staff!SCHEDULE_RESPONSE,param1,appointments,0;
}

/* Main Booking System Process*/ 
proctype BookingSystem() {
	mtype msg_type;
	int param1,param2,param3;
	
	do
	:: user_to_system ? msg_type, param1, param2, param3 -> 
		if  :: msg_type == BOOK_REQUEST -> 
			    book_appointment(msg_type, param1, param2);
			
		    :: msg_type == CANCEL_REQUEST -> 
			    cancel_appointment(param1,param2);
			
		    :: msg_type == RESCHEDULE_REQUEST -> 
			    reschedule_appointment(param1,param2,param3);
		fi
		
	:: staff_to_system ? msg_type,param1,param2,param3 -> 
		if  :: msg_type == UPDATE_AVAILABILITY -> 
			update_staff_availability(param1,param2,param3);
		fi
	od
}



/* User Process*/ 
proctype User(int user_id) {
	mtype msg_type;
	int param1,param2,response;
	
	do
	:: /* Book appointment*/ 
		user_to_system ! BOOK_REQUEST, user_id, 3;
		system_to_user ? msg_type, param1, param2, response;
		assert(msg_type == BOOK_RESPONSE);
		
	:: /* Cancel appointment*/ 
		user_to_system ! CANCEL_REQUEST, user_id, 1, 0;
		system_to_user ? msg_type, param1, param2, response;
		assert(msg_type == CANCEL_RESPONSE);
		
	:: /* Reschedule appointment */ 
		user_to_system ! RESCHEDULE_REQUEST, user_id, 1, 2;
		system_to_user ? msg_type, param1, param2, response;
		assert(msg_type == RESCHEDULE_RESPONSE);
		
	:: break
	od
}

/* Staff Process*/ 
proctype Staff(int staff_id) {
	mtype msg_type;
	int param1,param2,response;
	
	do
	:: /* Update availability*/ 
		staff_to_system ! UPDATE_AVAILABILITY, staff_id, 1, 1;
		system_to_staff ? msg_type, param1, param2, response;
		assert(msg_type == AVAILABILITY_UPDATED);
	:: break 
	od
}