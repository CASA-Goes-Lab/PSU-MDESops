from DESops.automata.event import Event


def inserted_event(event):
    """
    Creates a new event matching the given label with the
        insered=True
        deleted=False
    Accepts either str (label) or Event as inputs
    """
    if isinstance(event, Event):
        label = event.label
    else:
        label = event
    return Event(label, inserted=True, deleted=False)


def deleted_event(event):
    """
    Creates a new event matching the given label with the
        insered=False
        deleted=True
    Accepts either str (label) or Event as inputs
    """
    if isinstance(event, Event):
        label = event.label
    else:
        label = event
    return Event(label, inserted=False, deleted=True)


def unedited_event(event):
    """
    Creates an event matching label of given event and without any attributes
    """
    if isinstance(event, Event):
        label = event.label
    else:
        label = event
    return Event(label)


def is_deleted(event):
    """
    Returns whether an event has deleted : True attr
    """
    if "deleted" in event.__dict__:
        return event.deleted
    return False


def is_inserted(event):
    """
    Returns whether an event has inserted : True attr
    """
    if "inserted" in event.__dict__:
        return event.inserted
    return False


def is_unedited(event):
    """
    Returns whether an event has no true-valued attributes.
    This implies it is neither inserted nor deleted

    """
    if len(event.__dict__) == 1:
        # Most events will only have the label attribute
        return True

    return not is_deleted(event) and not is_inserted(event)
